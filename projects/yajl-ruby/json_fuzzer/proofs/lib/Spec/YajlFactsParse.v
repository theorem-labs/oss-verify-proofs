(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlDecode
     YajlParser YajlFactsBuf YajlFactsLex YajlFactsDecode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_map_state (s : ystate) : bool :=
  match s with
  | ST_map_start | ST_map_sep | ST_map_need_val | ST_map_got_val | ST_map_need_key => true
  | _ => false
  end.
Definition is_array_state (s : ystate) : bool :=
  match s with ST_array_start | ST_array_got_val | ST_array_need_val => true | _ => false end.
Definition is_frame (s : ystate) : bool := is_map_state s || is_array_state s.
Definition is_error_state (s : ystate) : bool :=
  match s with ST_parse_error | ST_lexical_error => true | _ => false end.

Fixpoint count_map (l : list ystate) : Z :=
  match l with [] => 0 | s :: r => (if is_map_state s then 1 else 0) + count_map r end.
Fixpoint count_array (l : list ystate) : Z :=
  match l with [] => 0 | s :: r => (if is_array_state s then 1 else 0) + count_array r end.

Lemma count_map_nonneg : forall l, 0 <= count_map l.
Proof. induction l; cbn; [lia|]. destruct (is_map_state a); lia. Qed.
Lemma count_array_nonneg : forall l, 0 <= count_array l.
Proof. induction l; cbn; [lia|]. destruct (is_array_state a); lia. Qed.
Lemma count_map_le : forall l, count_map l <= zlength l.
Proof. induction l; cbn; [lia|]. unfold zlength in *; cbn [length]. destruct (is_map_state a); lia. Qed.
Lemma count_array_le : forall l, count_array l <= zlength l.
Proof. induction l; cbn; [lia|]. unfold zlength in *; cbn [length]. destruct (is_array_state a); lia. Qed.

(* [comment removed for export] *)
Fixpoint frames_ok (l : list ystate) : Prop :=
  match l with
  | [] => False
  | s :: rest => match rest with
                 | [] => s = ST_start
                 | _ => is_frame s = true /\ frames_ok rest
                 end
  end.

Lemma frames_ok_cons : forall s rest, is_frame s = true -> frames_ok rest -> frames_ok (s :: rest).
Proof. intros s [|x r] Hs Hr; cbn in *; [contradiction|auto]. Qed.

Lemma frames_ok_inv : forall s rest, frames_ok (s :: rest) ->
  (s = ST_start /\ rest = []) \/ (is_frame s = true /\ frames_ok rest).
Proof. intros s [|x r] H; cbn in H; auto. Qed.

Lemma frames_ok_not_error : forall s rest, frames_ok (s :: rest) -> is_error_state s = false.
Proof.
  intros s rest H. destruct (frames_ok_inv _ _ H) as [[-> _]|[Hf _]]; auto.
  destruct s; cbn in *; auto; discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stack_inv (h : yhandle) (cx : yctx) : Prop :=
  frames_ok (h_stack h) /\ h_used h <= h_stack_size h /\ h_stack_blk h <> None /\
  (exists k, 0 < k /\ h_stack_size h = YAJL_BS_INC * k) /\
  cx_objectLevel cx = count_map (h_stack h) /\ cx_arrayLevel cx = count_array (h_stack h).

Definition hinv (len : Z) (h : yhandle) (cx : yctx) : Prop :=
  lex_inv (h_lexer h) /\ 0 <= h_bytesConsumed h <= len /\
  buf_inv (h_decbuf h) /\ yb_state (h_decbuf h) = BS_ok /\
  stack_inv h cx /\
  h_used h <= h_bytesConsumed h + 1 /\            (* [comment removed for export] *)
  h_stack_size h <= len + 1 + YAJL_BS_INC.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition weak_inv (len : Z) (h : yhandle) : Prop :=
  h_stack h <> [] /\ h_used h <= h_stack_size h /\ 0 <= h_bytesConsumed h <= len /\
  buf_inv (h_decbuf h) /\ buf_inv (lx_buf (h_lexer h)) /\ h_used h <= len + 1 /\
  h_stack_size h <= len + 1 + YAJL_BS_INC.

Lemma hinv_weak : forall len h cx, hinv len h cx -> weak_inv len h.
Proof.
  intros len h cx (Hlx & Hoff & Hdb & Hdbs & (Hfr & Hus & Hblk & Hk & Ho & Ha) & Hdepth & Hsize).
  refine (conj _ (conj Hus (conj Hoff (conj Hdb (conj _ (conj _ Hsize)))))).
  - destruct (h_stack h); cbn in Hfr; [contradiction|congruence].
  - destruct Hlx as (_&_&_&_&_&_& ->). apply buf_inv_zero.
  - lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma h_used_cons : forall h s rest, h_used (h_set_stack h (s :: rest)) = 1 + zlength rest.
Proof. intros. unfold h_used, zlength; cbn [h_stack h_set_stack length]. lia. Qed.

Lemma zlength_cons : forall {A} (x : A) l, zlength (x :: l) = 1 + zlength l.
Proof. intros. unfold zlength; cbn [length]. lia. Qed.

Lemma ybs_current_eq : forall h s rest, h_stack h = s :: rest -> ybs_current h = YRet s.
Proof. intros h s rest E. unfold ybs_current. rewrite E. reflexivity. Qed.

Lemma ybs_set_eq : forall h s rest s', h_stack h = s :: rest -> h_used h <= h_stack_size h ->
  ybs_set h s' = YRet (h_set_stack h (s' :: rest)).
Proof.
  intros h s rest s' E Hu. unfold ybs_set. rewrite E.
  destruct (Z.leb_spec (h_used h) (h_stack_size h)); [reflexivity|lia].
Qed.

Lemma ybs_pop_eq : forall h s rest, h_stack h = s :: rest -> ybs_pop h = YRet (h_set_stack h rest).
Proof. intros h s rest E. unfold ybs_pop. rewrite E. reflexivity. Qed.

Lemma ybs_push_post : forall h s,
  h_used h <= h_stack_size h -> h_stack_blk h <> None ->
  (exists k, 0 < k /\ h_stack_size h = YAJL_BS_INC * k) ->
  ypost (ybs_push h s)
    (fun r => let '(ok, h') := r in
      h_lexer h' = h_lexer h /\ h_bytesConsumed h' = h_bytesConsumed h /\ h_decbuf h' = h_decbuf h /\
      h_parseError h' = h_parseError h /\ h_blk h' = h_blk h /\ h_lexer_blk h' = h_lexer_blk h /\
      h_decbuf_blk h' = h_decbuf_blk h /\
      h_used h' <= h_stack_size h' /\
      (exists k, 0 < k /\ h_stack_size h' = YAJL_BS_INC * k) /\
      (h_stack_size h' = h_stack_size h \/
       (h_stack_size h' = h_stack_size h + YAJL_BS_INC /\ h_used h = h_stack_size h)) /\
      if ok then h_stack h' = s :: h_stack h /\ h_stack_blk h' <> None
      else h_stack h' = h_stack h).
Proof.
  intros h s Hu Hb [k [Hk Hsz]]. unfold ybs_push. unfold h_used, YAJL_BS_INC in *.
  destruct (Z.eqb_spec (h_stack_size h - zlength (h_stack h)) 0).
  - destruct (Z.ltb_spec (UINT_MAX - 128) (h_stack_size h)).
    + cbn -[Z.add Z.mul zlength]. repeat split; auto. exists k; auto.
    + cbn -[Z.add Z.mul zlength]. intros [p|]; cbn -[Z.add Z.mul zlength].
      * rewrite zlength_cons.
        repeat split; try lia; try congruence. exists (k + 1). lia.
      * repeat split; try lia. exists (k + 1). lia.
  - cbn -[Z.add Z.mul zlength].
    rewrite zlength_cons. repeat split; auto; try lia. exists k; auto.
Qed.

Definition step_post (len off0 : Z) (r : step_res) : Prop :=
  match r with
  | SR_done st h' cx' => weak_inv len h'
  | SR_again h' cx' =>
      (hinv len h' cx' /\ off0 < h_bytesConsumed h') \/
      (weak_inv len h' /\ exists s rest, h_stack h' = s :: rest /\ is_error_state s = true)
  end.

Ltac splits := repeat match goal with |- _ /\ _ => split end.

Lemma lex_inv_buf_inv : forall lx, lex_inv lx -> buf_inv (lx_buf lx).
Proof. intros lx (_&_&_&_&_&_& ->). apply buf_inv_zero. Qed.

Lemma ygot_value_post : forall len off0 h cx push s rest,
  h_stack h = s :: rest ->
  (s = ST_start \/ s = ST_map_need_val \/ s = ST_array_need_val \/ s = ST_array_start) ->
  lex_inv (h_lexer h) -> 0 <= h_bytesConsumed h <= len -> off0 < h_bytesConsumed h ->
  buf_inv (h_decbuf h) -> yb_state (h_decbuf h) = BS_ok ->
  frames_ok (h_stack h) -> h_used h <= h_stack_size h -> h_stack_blk h <> None ->
  (exists k, 0 < k /\ h_stack_size h = YAJL_BS_INC * k) -> h_used h <= off0 + 1 ->
  h_stack_size h <= len + 1 + YAJL_BS_INC ->
  match push with
  | None => cx_objectLevel cx = count_map (h_stack h) /\ cx_arrayLevel cx = count_array (h_stack h)
  | Some ST_map_start => cx_objectLevel cx = count_map (h_stack h) + 1 /\ cx_arrayLevel cx = count_array (h_stack h)
  | Some ST_array_start => cx_objectLevel cx = count_map (h_stack h) /\ cx_arrayLevel cx = count_array (h_stack h) + 1
  | Some _ => False
  end ->
  ypost (ygot_value h cx push) (step_post len off0).
Proof.
  intros len off0 h cx push s rest Hst Hs Hlx Hoff Hprog Hdb Hdbs Hfr Hus Hblk Hk Hdepth Hsize Hcx.
  unfold ygot_value. rewrite (ybs_current_eq h s rest Hst). cbn [ybind].
  (* [comment removed for export] *)
  eapply (ypost_bind _ _
    (fun h1 => lex_inv (h_lexer h1) /\ h_bytesConsumed h1 = h_bytesConsumed h /\
               h_decbuf h1 = h_decbuf h /\ h_stack_size h1 = h_stack_size h /\
               h_stack_blk h1 = h_stack_blk h /\
               exists s1, h_stack h1 = s1 :: rest /\ frames_ok (h_stack h1) /\
                 count_map (h_stack h1) = count_map (h_stack h) /\
                 count_array (h_stack h1) = count_array (h_stack h))).
  { destruct Hs as [-> | [-> | [-> | ->]]].
    - eapply ypost_bind. { apply ylex_realloc_post; auto. }
      intros lx' (Hlx' & _ & _). cbn. splits; auto. exists ST_start. rewrite Hst. splits; auto.
      rewrite <- Hst; auto.
    - rewrite (ybs_set_eq h _ rest _ Hst Hus). cbn. splits; auto. exists ST_map_got_val. splits; auto.
      + rewrite Hst in Hfr. destruct (frames_ok_inv _ _ Hfr) as [[? _]|[_ Hr]]; [discriminate|].
        apply frames_ok_cons; auto.
      + rewrite Hst; reflexivity.
      + rewrite Hst; reflexivity.
    - rewrite (ybs_set_eq h _ rest _ Hst Hus). cbn. splits; auto. exists ST_array_got_val. splits; auto.
      + rewrite Hst in Hfr. destruct (frames_ok_inv _ _ Hfr) as [[? _]|[_ Hr]]; [discriminate|].
        apply frames_ok_cons; auto.
      + rewrite Hst; reflexivity.
      + rewrite Hst; reflexivity.
    - rewrite (ybs_set_eq h _ rest _ Hst Hus). cbn. splits; auto. exists ST_array_got_val. splits; auto.
      + rewrite Hst in Hfr. destruct (frames_ok_inv _ _ Hfr) as [[? _]|[_ Hr]]; [discriminate|].
        apply frames_ok_cons; auto.
      + rewrite Hst; reflexivity.
      + rewrite Hst; reflexivity. }
  intros h1 (Hlx1 & Hoff1 & Hdb1 & Hsz1 & Hblk1 & (s1 & Hst1 & Hfr1 & Hcm1 & Hca1)).
  assert (Hus1 : h_used h1 <= h_stack_size h1).
  { unfold h_used in *. rewrite Hst1, Hsz1. rewrite Hst in Hus. rewrite zlength_cons in *. lia. }
  destruct push as [st|].
  - eapply ypost_bind.
    { apply ybs_push_post; auto. rewrite Hblk1; auto. rewrite Hsz1; auto. }
    intros [ok h2] (HL & HO & HD & _ & _ & _ & _ & HU & HK & HS & Hok).
    destruct ok.
    + destruct Hok as [Hst2 Hblk2]. cbn. left. split; [|rewrite HO, Hoff1; lia].
      unfold hinv, stack_inv. rewrite HL, HO, HD, Hst2, Hoff1, Hdb1.
      splits; auto; try lia.
      * apply frames_ok_cons; auto. destruct st; try contradiction; reflexivity.
      * destruct st; try contradiction; cbn [count_map is_map_state] in *; lia.
      * destruct st; try contradiction; cbn [count_array is_array_state] in *; lia.
      * unfold h_used in *. rewrite Hst2, Hst1, !zlength_cons. rewrite Hst, zlength_cons in Hdepth. lia.
      * unfold h_used in *. rewrite Hst1, Hsz1 in HS. rewrite Hst in Hdepth. rewrite zlength_cons in *. lia.
    + cbn. unfold weak_inv. rewrite HO, HD, HL, Hoff1, Hdb1. unfold h_used in HU, Hdepth, HS |- *.
      rewrite Hok, Hst1 in HU |- *. rewrite Hst1, Hsz1 in HS. rewrite Hst in Hdepth. rewrite zlength_cons in *.
      splits; auto; try lia; try congruence. apply lex_inv_buf_inv; auto.
  - cbn. left. split; [|rewrite Hoff1; lia].
    unfold hinv, stack_inv. rewrite Hoff1, Hdb1, Hsz1, Hblk1, Hcm1, Hca1.
    splits; auto; try lia.
    unfold h_used in *. rewrite Hst1, zlength_cons. rewrite Hst, zlength_cons in Hdepth. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac hproj := cbn [h_stack h_lexer h_bytesConsumed h_decbuf h_stack_size h_stack_blk h_parseError
                   h_blk h_lexer_blk h_decbuf_blk
                   h_set_lex_off h_set_off h_set_perr h_set_decbuf h_set_stack h_set_stack3 h_set_lexer] in *.

Ltac weak_tac :=
  unfold weak_inv, h_used in *; hproj; splits; auto; try lia; try congruence;
  try (apply lex_inv_buf_inv; assumption).
Ltac weak_tac2 Hst :=
  unfold weak_inv, h_used in *; hproj;
  try match type of Hst with h_stack ?hh = _ :: _ =>
        repeat match goal with Hu : zlength (h_stack hh) <= _ |- _ => rewrite Hst, zlength_cons in Hu end end;
  rewrite ?zlength_cons in *; splits; auto; try lia; try congruence;
  try (apply lex_inv_buf_inv; assumption).

Lemma sbody_ix_slice : forall txt i n, 0 <= i -> sbody_ix txt i (i + n) -> sbody_ix (zslice txt i n) 0 n.
Proof.
  intros txt i n Hi Hb. pose proof (sbody_ix_shift txt i (i + n) Hb i n Hi ltac:(lia) ltac:(lia)) as H.
  replace (i - i) with 0 in H by lia. replace (i + n - i) with n in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma ydecode_tok_post : forall h bytes n,
  buf_inv (h_decbuf h) -> yb_state (h_decbuf h) = BS_ok -> sbody_ix bytes 0 n -> 0 <= n -> n < 2^40 ->
  ypost (ydecode_tok h bytes n)
        (fun h1 => exists db, h1 = h_set_decbuf h db /\ buf_inv db /\ yb_used db <= n).
Proof.
  intros h bytes n Hinv Hok Hbody Hn Hn40. unfold ydecode_tok.
  eapply ypost_bind. { apply ybuf_clear_post; eauto. }
  intros db [Hinv0 ->].
  eapply ypost_bind.
  { apply ystring_decode_post; eauto. cbn -[Z.pow Z.mul]. lia. }
  intros db [Hinv1 Hu1]. cbn in Hu1. cbn. exists db. auto.
Qed.

(* [comment removed for export] *)
Definition pre (len off0 : Z) (h' : yhandle) : Prop :=
  lex_inv (h_lexer h') /\ 0 <= h_bytesConsumed h' <= len /\ off0 < h_bytesConsumed h' /\
  buf_inv (h_decbuf h') /\ yb_state (h_decbuf h') = BS_ok /\
  h_used h' <= h_stack_size h' /\ h_stack_blk h' <> None /\
  (exists k, 0 < k /\ h_stack_size h' = YAJL_BS_INC * k) /\ h_used h' <= off0 + 1 /\
  h_stack_size h' <= len + 1 + YAJL_BS_INC.

Lemma set_frame_again : forall len off0 h' cx s rest s',
  h_stack h' = s :: rest -> frames_ok (s :: rest) -> is_frame s = true -> is_frame s' = true ->
  is_map_state s' = is_map_state s -> is_array_state s' = is_array_state s ->
  pre len off0 h' ->
  cx_objectLevel cx = count_map (s :: rest) -> cx_arrayLevel cx = count_array (s :: rest) ->
  ypost (h1 <- ybs_set h' s' ;; YRet (SR_again h1 cx)) (step_post len off0).
Proof.
  intros len off0 h' cx s rest s' Hst Hfr Hs Hs' Hm Ha (Hlx & Hoff & Hprog & Hdb & Hdbs & Hus & Hblk & Hk & Hdepth & Hsize) Ho Hao.
  rewrite (ybs_set_eq h' s rest s' Hst Hus). cbn. left.
  split; [|lia]. unfold hinv, stack_inv, h_used in *. hproj. rewrite Hst in Hus, Hdepth.
  rewrite !zlength_cons in *. cbn [count_map count_array] in *. rewrite Hm, Ha.
  splits; auto; try lia.
  destruct (frames_ok_inv _ _ Hfr) as [[-> _]|[_ Hr]]; [discriminate|]. apply frames_ok_cons; auto.
Qed.

Lemma pop_again : forall len off0 h' cx s rest,
  h_stack h' = s :: rest -> frames_ok (s :: rest) -> is_frame s = true ->
  pre len off0 h' ->
  cx_objectLevel cx = count_map rest -> cx_arrayLevel cx = count_array rest ->
  ypost (h1 <- ybs_pop h' ;; YRet (SR_again h1 cx)) (step_post len off0).
Proof.
  intros len off0 h' cx s rest Hst Hfr Hs (Hlx & Hoff & Hprog & Hdb & Hdbs & Hus & Hblk & Hk & Hdepth & Hsize) Ho Hao.
  rewrite (ybs_pop_eq h' s rest Hst). cbn. left.
  split; [|lia]. unfold hinv, stack_inv, h_used in *. hproj. rewrite Hst in Hus, Hdepth.
  rewrite !zlength_cons in *.
  splits; auto; try lia.
  destruct (frames_ok_inv _ _ Hfr) as [[-> _]|[_ Hr]]; [discriminate|]. auto.
Qed.

(* [comment removed for export] *)
Lemma set_error_again : forall len off0 h' cx s rest e (F : yhandle -> yhandle),
  h_stack h' = s :: rest -> is_error_state e = true ->
  h_used h' <= h_stack_size h' -> 0 <= h_bytesConsumed h' <= len ->
  buf_inv (h_decbuf h') -> buf_inv (lx_buf (h_lexer h')) -> h_used h' <= len + 1 ->
  h_stack_size h' <= len + 1 + YAJL_BS_INC ->
  (forall h1, 0 <= h_bytesConsumed h1 <= len ->
              h_stack (F h1) = h_stack h1 /\ h_stack_size (F h1) = h_stack_size h1 /\
              h_decbuf (F h1) = h_decbuf h1 /\ h_lexer (F h1) = h_lexer h1 /\
              0 <= h_bytesConsumed (F h1) <= len) ->
  ypost (h1 <- ybs_set h' e ;; YRet (SR_again (F h1) cx)) (step_post len off0).
Proof.
  intros len off0 h' cx s rest e F Hst He Hus Hoff Hdb Hlb Hul Hsz HF.
  rewrite (ybs_set_eq h' s rest e Hst Hus). cbn -[Z.add Z.sub]. right.
  destruct (HF (h_set_stack h' (e :: rest)) ltac:(hproj; lia)) as (F1 & F2 & F3 & F4 & F5).
  split.
  - unfold weak_inv, h_used in *. rewrite F1, F2, F3, F4. hproj. rewrite Hst in Hus, Hul.
    rewrite zlength_cons in *. splits; auto; try lia. congruence.
  - rewrite F1. hproj. exists e, rest. auto.
Qed.

Lemma done_weak : forall len off0 st h' cx,
  h_stack h' <> [] -> h_used h' <= h_stack_size h' -> 0 <= h_bytesConsumed h' <= len ->
  buf_inv (h_decbuf h') -> buf_inv (lx_buf (h_lexer h')) -> h_used h' <= len + 1 ->
  h_stack_size h' <= len + 1 + YAJL_BS_INC ->
  ypost (YRet (SR_done st h' cx)) (step_post len off0).
Proof. intros. cbn. unfold weak_inv. splits; auto; lia. Qed.

Lemma lex_err_bufinv : forall (lx : ylexer) (P Q A B C D : Prop),
  P /\ Q /\ (lex_inv lx \/ (A /\ B /\ buf_inv (lx_buf lx) /\ C /\ D)) -> buf_inv (lx_buf lx).
Proof. intros lx P Q A B C D (_&_&[H|(_&_&H&_)]); [apply lex_inv_buf_inv|]; auto. Qed.

Theorem yparse_step_post : forall txt len h cx,
  len = zlength txt -> len < 2^32 -> hinv len h cx ->
  ypost (yparse_step jf_callbacks txt len h cx) (step_post len (h_bytesConsumed h)).
Proof.
  intros txt len h cx Hlen H32 Hinv.
  destruct Hinv as (Hlx & Hoff & Hdb & Hdbs & (Hfr & Hus & Hblk & Hk & Ho & Ha) & Hdepth & Hsize).
  unfold h_used in Hdepth.
  destruct (h_stack h) as [|s rest] eqn:Hst; [contradiction|]. rewrite <- Hst in Hdepth.
  unfold yparse_step. rewrite (ybs_current_eq h s rest Hst). cbn [ybind].
  pose proof (frames_ok_inv _ _ Hfr) as Hcase.
  assert (HLEX : ypost (ylex_lex (h_lexer h) txt len (h_bytesConsumed h)) (lex_post txt len (h_bytesConsumed h))).
  { apply ylex_lex_post; auto. }
  pose proof (lex_inv_buf_inv _ Hlx) as Hlb.
  unfold h_used in Hus.
  set (off0 := h_bytesConsumed h) in *.
  (* [comment removed for export] *)
  Ltac lexstep HLEX :=
    eapply ypost_bind; [exact HLEX|];
    intros [[[[lx tok] off] ob] n] (Hoff' & Hac' & Hv' & Htok).
  Ltac mkpre len off0 h lx off Hst :=
    assert (HP : pre len off0 (h_set_lex_off h lx off))
      by (unfold pre, h_used; hproj; splits; auto; try lia; tauto).
  Ltac leaf_done := apply done_weak; unfold h_used; hproj; auto; try lia; try congruence;
                    try (eapply lex_err_bufinv; eassumption); try (apply lex_inv_buf_inv; tauto).
  Ltac leaf_error Hst :=
    eapply set_error_again; [hproj; exact Hst | reflexivity | unfold h_used; hproj; lia | hproj; lia
                            | hproj; assumption | hproj | unfold h_used; hproj; lia | hproj; lia
                            | intros; hproj; splits; auto; lia];
    first [eapply lex_err_bufinv; eassumption | apply lex_inv_buf_inv; tauto].
  Ltac s_member :=
    first [ left; reflexivity | right; left; reflexivity
          | right; right; left; reflexivity | right; right; right; reflexivity ].
  Ltac counts Hst :=
    hproj; rewrite ?Hst; cbn [count_map count_array is_map_state is_array_state cx_arrayLevel cx_objectLevel] in *;
    splits; lia.
  (* [comment removed for export] *)
  Ltac go_value Hst Hfr :=
    eapply ygot_value_post;
    [ hproj; exact Hst | s_member | hproj; tauto | hproj; lia | hproj; lia | hproj; assumption
    | hproj; first [assumption | reflexivity] | hproj; rewrite Hst; exact Hfr | unfold h_used; hproj; lia
    | hproj; assumption | hproj; assumption | unfold h_used; hproj; lia | hproj; lia | counts Hst ].
  destruct s; cbn [state_code Z.eqb Pos.eqb].
  - (* [comment removed for export] *)
    lexstep HLEX.
    destruct tok; try contradiction; unfold yparse_error.
    + (* [comment removed for export] *) cbn [cb_boolean jf_callbacks ybind]. go_value Hst Hfr.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) leaf_done. tauto.
    + (* [comment removed for export] *) leaf_error Hst.
    + (* [comment removed for export] *) cbn [cb_start_array jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_start_map jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_null jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *)
      rewrite (ybs_current_eq (h_set_lex_off h lx off) _ rest ltac:(hproj; exact Hst)).
      cbn [ybind state_eqb state_code Z.eqb Pos.eqb]. unfold yparse_error.
      mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) cbn [cb_number jf_callbacks ybind]. unfold yassert.
      destruct (Z.ltb_spec 0 n); [|exfalso; destruct Htok as (_&_&(?&?&?&?&?&?&?)); lia]. cbn [ybind].
      go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_number jf_callbacks ybind]. unfold yassert.
      destruct (Z.ltb_spec 0 n); [|exfalso; destruct Htok as (_&_&(?&?&?&?&?&?&?)); lia]. cbn [ybind].
      go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_string jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *)
      destruct Htok as (Hlx' & Hprog & (i & Hob & Hi & Hn & Hin & H1 & Hq1 & Hq2 & Hend & Hbody)).
      subst ob. cbn [out_bytes].
      eapply ypost_bind.
      { apply (ydecode_tok_post (h_set_lex_off h lx off) (zslice txt i n) n); hproj; auto; try lia.
        apply sbody_ix_slice; auto; lia. }
      intros h1 (db & -> & Hdbi & Hdbu). unfold ybuf_err. hproj.
      destruct (yb_state db) eqn:Hdbs'; cbn [buf_state_ok negb].
      * unfold ybuf_data_chk, ybuf_len_chk. rewrite Hdbs'. cbn [ybind cb_string jf_callbacks].
        eapply ygot_value_post;
        [ hproj; exact Hst | s_member | hproj; tauto | hproj; lia | hproj; lia | hproj; assumption
        | hproj; first [assumption | reflexivity] | hproj; rewrite Hst; exact Hfr | unfold h_used; hproj; lia
        | hproj; assumption | hproj; assumption | unfold h_used; hproj; lia | hproj; lia | counts Hst ].
      * unfold ybuf_chk_fail.
        rewrite (ybs_set_eq (h_set_decbuf (h_set_lex_off h lx off) db) _ rest _
                   ltac:(hproj; exact Hst) ltac:(unfold h_used; hproj; lia)). cbn.
        weak_tac2 Hst.
      * unfold ybuf_chk_fail.
        rewrite (ybs_set_eq (h_set_decbuf (h_set_lex_off h lx off) db) _ rest _
                   ltac:(hproj; exact Hst) ltac:(unfold h_used; hproj; lia)). cbn.
        weak_tac2 Hst.
  - exfalso. destruct Hcase as [[? _]|[? _]]; discriminate.
  - exfalso. destruct Hcase as [[? _]|[? _]]; discriminate.
  - exfalso. destruct Hcase as [[? _]|[? _]]; discriminate.
  - (* [comment removed for export] *)
    lexstep HLEX.
    pose proof (count_map_nonneg rest) as Hcr. 
    assert (Hol : 0 < cx_objectLevel cx) by (rewrite Ho; cbn [count_map is_map_state]; lia).
    destruct tok; try contradiction; unfold yparse_error.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) leaf_done. tauto.
    + (* [comment removed for export] *) leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *)
      rewrite (ybs_current_eq (h_set_lex_off h lx off) _ rest ltac:(hproj; exact Hst)).
      cbn [ybind state_eqb state_code Z.eqb Pos.eqb cb_end_map jf_callbacks yassert].
      destruct (Z.ltb_spec 0 (cx_objectLevel cx)); [|lia]. cbn [ybind].
      mkpre len off0 h lx off Hst.
      eapply pop_again; [hproj; exact Hst | exact Hfr | reflexivity | exact HP | counts Hst | counts Hst].
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) cbn [cb_map_key jf_callbacks ybind yassert].
      destruct (Z.ltb_spec 0 (cx_objectLevel cx)); [|lia]. cbn [ybind].
      mkpre len off0 h lx off Hst.
      eapply set_frame_again; try (hproj; first [exact Hst | exact Hfr | reflexivity | exact HP]); cbn; auto.
    + (* [comment removed for export] *)
      destruct Htok as (Hlx' & Hprog & (i & Hob & Hi & Hn & Hin & H1 & Hq1 & Hq2 & Hend & Hbody)).
      subst ob. cbn [out_bytes].
      eapply ypost_bind.
      { apply (ydecode_tok_post (h_set_lex_off h lx off) (zslice txt i n) n); hproj; auto; try lia.
        apply sbody_ix_slice; auto; lia. }
      intros h1 (db & -> & Hdbi & Hdbu). unfold ybuf_err. hproj.
      destruct (yb_state db) eqn:Hdbs'; cbn [buf_state_ok negb].
      * unfold ybuf_data_chk, ybuf_len_chk. rewrite Hdbs'. cbn [ybind cb_map_key jf_callbacks yassert].
        destruct (Z.ltb_spec 0 (cx_objectLevel cx)); [|lia]. cbn [ybind].
        assert (HP : pre len off0 (h_set_decbuf (h_set_lex_off h lx off) db))
          by (unfold pre, h_used; hproj; splits; auto; try lia).
        eapply set_frame_again; try (hproj; first [exact Hst | exact Hfr | reflexivity | exact HP]); cbn; auto.
      * unfold ybuf_chk_fail.
        rewrite (ybs_set_eq (h_set_decbuf (h_set_lex_off h lx off) db) _ rest _
                   ltac:(hproj; exact Hst) ltac:(unfold h_used; hproj; lia)). cbn.
        weak_tac2 Hst.
      * unfold ybuf_chk_fail.
        rewrite (ybs_set_eq (h_set_decbuf (h_set_lex_off h lx off) db) _ rest _
                   ltac:(hproj; exact Hst) ltac:(unfold h_used; hproj; lia)). cbn.
        weak_tac2 Hst.
  - (* [comment removed for export] *)
    lexstep HLEX.
    destruct tok; try contradiction; unfold yparse_error.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) mkpre len off0 h lx off Hst.
      eapply set_frame_again; try (hproj; first [exact Hst | exact Hfr | reflexivity | exact HP]); cbn; auto.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) leaf_done. tauto.
    + (* [comment removed for export] *) leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
  - (* [comment removed for export] *)
    lexstep HLEX.
    destruct tok; try contradiction; unfold yparse_error.
    + (* [comment removed for export] *) cbn [cb_boolean jf_callbacks ybind]. go_value Hst Hfr.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) leaf_done. tauto.
    + (* [comment removed for export] *) leaf_error Hst.
    + (* [comment removed for export] *) cbn [cb_start_array jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_start_map jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_null jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *)
      rewrite (ybs_current_eq (h_set_lex_off h lx off) _ rest ltac:(hproj; exact Hst)).
      cbn [ybind state_eqb state_code Z.eqb Pos.eqb]. unfold yparse_error.
      mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) cbn [cb_number jf_callbacks ybind]. unfold yassert.
      destruct (Z.ltb_spec 0 n); [|exfalso; destruct Htok as (_&_&(?&?&?&?&?&?&?)); lia]. cbn [ybind].
      go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_number jf_callbacks ybind]. unfold yassert.
      destruct (Z.ltb_spec 0 n); [|exfalso; destruct Htok as (_&_&(?&?&?&?&?&?&?)); lia]. cbn [ybind].
      go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_string jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *)
      destruct Htok as (Hlx' & Hprog & (i & Hob & Hi & Hn & Hin & H1 & Hq1 & Hq2 & Hend & Hbody)).
      subst ob. cbn [out_bytes].
      eapply ypost_bind.
      { apply (ydecode_tok_post (h_set_lex_off h lx off) (zslice txt i n) n); hproj; auto; try lia.
        apply sbody_ix_slice; auto; lia. }
      intros h1 (db & -> & Hdbi & Hdbu). unfold ybuf_err. hproj.
      destruct (yb_state db) eqn:Hdbs'; cbn [buf_state_ok negb].
      * unfold ybuf_data_chk, ybuf_len_chk. rewrite Hdbs'. cbn [ybind cb_string jf_callbacks].
        eapply ygot_value_post;
        [ hproj; exact Hst | s_member | hproj; tauto | hproj; lia | hproj; lia | hproj; assumption
        | hproj; first [assumption | reflexivity] | hproj; rewrite Hst; exact Hfr | unfold h_used; hproj; lia
        | hproj; assumption | hproj; assumption | unfold h_used; hproj; lia | hproj; lia | counts Hst ].
      * unfold ybuf_chk_fail.
        rewrite (ybs_set_eq (h_set_decbuf (h_set_lex_off h lx off) db) _ rest _
                   ltac:(hproj; exact Hst) ltac:(unfold h_used; hproj; lia)). cbn.
        weak_tac2 Hst.
      * unfold ybuf_chk_fail.
        rewrite (ybs_set_eq (h_set_decbuf (h_set_lex_off h lx off) db) _ rest _
                   ltac:(hproj; exact Hst) ltac:(unfold h_used; hproj; lia)). cbn.
        weak_tac2 Hst.
  - (* [comment removed for export] *)
    lexstep HLEX.
    pose proof (count_map_nonneg rest) as Hcr.
    assert (Hol : 0 < cx_objectLevel cx) by (rewrite Ho; cbn [count_map is_map_state]; lia).
    Ltac restore_err Hst Htok :=
      decompose [ex and] Htok;
      eapply set_error_again; [hproj; exact Hst | reflexivity | unfold h_used; hproj; lia | hproj; lia
                              | hproj; assumption | hproj | unfold h_used; hproj; lia | hproj; lia
                              | intros; hproj; splits; auto;
                                match goal with |- context [?a <=? ?b] => destruct (Z.leb_spec a b) end; lia];
      first [eapply lex_err_bufinv; eassumption | apply lex_inv_buf_inv; tauto].
    destruct tok; try contradiction.
    + mkpre len off0 h lx off Hst. restore_err Hst Htok.
    + mkpre len off0 h lx off Hst. restore_err Hst Htok.
    + (* [comment removed for export] *) mkpre len off0 h lx off Hst.
      eapply set_frame_again; try (hproj; first [exact Hst | exact Hfr | reflexivity | exact HP]); cbn; auto.
    + (* [comment removed for export] *) leaf_done. tauto.
    + (* [comment removed for export] *) leaf_error Hst.
    + mkpre len off0 h lx off Hst. restore_err Hst Htok.
    + mkpre len off0 h lx off Hst. restore_err Hst Htok.
    + mkpre len off0 h lx off Hst. restore_err Hst Htok.
    + mkpre len off0 h lx off Hst. restore_err Hst Htok.
    + (* [comment removed for export] *) cbn [cb_end_map jf_callbacks ybind yassert].
      destruct (Z.ltb_spec 0 (cx_objectLevel cx)); [|lia]. cbn [ybind].
      mkpre len off0 h lx off Hst.
      eapply pop_again; [hproj; exact Hst | exact Hfr | reflexivity | exact HP | counts Hst | counts Hst].
    + mkpre len off0 h lx off Hst. restore_err Hst Htok.
    + mkpre len off0 h lx off Hst. restore_err Hst Htok.
    + mkpre len off0 h lx off Hst. restore_err Hst Htok.
    + mkpre len off0 h lx off Hst. restore_err Hst Htok.
  - (* [comment removed for export] *)
    lexstep HLEX.
    pose proof (count_map_nonneg rest) as Hcr. 
    assert (Hol : 0 < cx_objectLevel cx) by (rewrite Ho; cbn [count_map is_map_state]; lia).
    destruct tok; try contradiction; unfold yparse_error.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) leaf_done. tauto.
    + (* [comment removed for export] *) leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *)
      rewrite (ybs_current_eq (h_set_lex_off h lx off) _ rest ltac:(hproj; exact Hst)).
      cbn [ybind state_eqb state_code Z.eqb Pos.eqb]. unfold yparse_error.
      mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) cbn [cb_map_key jf_callbacks ybind yassert].
      destruct (Z.ltb_spec 0 (cx_objectLevel cx)); [|lia]. cbn [ybind].
      mkpre len off0 h lx off Hst.
      eapply set_frame_again; try (hproj; first [exact Hst | exact Hfr | reflexivity | exact HP]); cbn; auto.
    + (* [comment removed for export] *)
      destruct Htok as (Hlx' & Hprog & (i & Hob & Hi & Hn & Hin & H1 & Hq1 & Hq2 & Hend & Hbody)).
      subst ob. cbn [out_bytes].
      eapply ypost_bind.
      { apply (ydecode_tok_post (h_set_lex_off h lx off) (zslice txt i n) n); hproj; auto; try lia.
        apply sbody_ix_slice; auto; lia. }
      intros h1 (db & -> & Hdbi & Hdbu). unfold ybuf_err. hproj.
      destruct (yb_state db) eqn:Hdbs'; cbn [buf_state_ok negb].
      * unfold ybuf_data_chk, ybuf_len_chk. rewrite Hdbs'. cbn [ybind cb_map_key jf_callbacks yassert].
        destruct (Z.ltb_spec 0 (cx_objectLevel cx)); [|lia]. cbn [ybind].
        assert (HP : pre len off0 (h_set_decbuf (h_set_lex_off h lx off) db))
          by (unfold pre, h_used; hproj; splits; auto; try lia).
        eapply set_frame_again; try (hproj; first [exact Hst | exact Hfr | reflexivity | exact HP]); cbn; auto.
      * unfold ybuf_chk_fail.
        rewrite (ybs_set_eq (h_set_decbuf (h_set_lex_off h lx off) db) _ rest _
                   ltac:(hproj; exact Hst) ltac:(unfold h_used; hproj; lia)). cbn.
        weak_tac2 Hst.
      * unfold ybuf_chk_fail.
        rewrite (ybs_set_eq (h_set_decbuf (h_set_lex_off h lx off) db) _ rest _
                   ltac:(hproj; exact Hst) ltac:(unfold h_used; hproj; lia)). cbn.
        weak_tac2 Hst.
  - (* [comment removed for export] *)
    lexstep HLEX.
    destruct tok; try contradiction; unfold yparse_error.
    + (* [comment removed for export] *) cbn [cb_boolean jf_callbacks ybind]. go_value Hst Hfr.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) leaf_done. tauto.
    + (* [comment removed for export] *) leaf_error Hst.
    + (* [comment removed for export] *) cbn [cb_start_array jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_start_map jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_null jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *)
      rewrite (ybs_current_eq (h_set_lex_off h lx off) _ rest ltac:(hproj; exact Hst)).
      cbn [ybind state_eqb state_code Z.eqb Pos.eqb cb_end_array jf_callbacks yassert].
      pose proof (count_array_nonneg rest) as Hcr. cbn [count_array is_array_state] in Ha.
      destruct (Z.ltb_spec 0 (cx_arrayLevel cx)); [|lia]. cbn [ybind].
      mkpre len off0 h lx off Hst.
      eapply pop_again; [hproj; exact Hst | exact Hfr | reflexivity | exact HP | counts Hst | counts Hst].
    + (* [comment removed for export] *) mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) cbn [cb_number jf_callbacks ybind]. unfold yassert.
      destruct (Z.ltb_spec 0 n); [|exfalso; destruct Htok as (_&_&(?&?&?&?&?&?&?)); lia]. cbn [ybind].
      go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_number jf_callbacks ybind]. unfold yassert.
      destruct (Z.ltb_spec 0 n); [|exfalso; destruct Htok as (_&_&(?&?&?&?&?&?&?)); lia]. cbn [ybind].
      go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_string jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *)
      destruct Htok as (Hlx' & Hprog & (i & Hob & Hi & Hn & Hin & H1 & Hq1 & Hq2 & Hend & Hbody)).
      subst ob. cbn [out_bytes].
      eapply ypost_bind.
      { apply (ydecode_tok_post (h_set_lex_off h lx off) (zslice txt i n) n); hproj; auto; try lia.
        apply sbody_ix_slice; auto; lia. }
      intros h1 (db & -> & Hdbi & Hdbu). unfold ybuf_err. hproj.
      destruct (yb_state db) eqn:Hdbs'; cbn [buf_state_ok negb].
      * unfold ybuf_data_chk, ybuf_len_chk. rewrite Hdbs'. cbn [ybind cb_string jf_callbacks].
        eapply ygot_value_post;
        [ hproj; exact Hst | s_member | hproj; tauto | hproj; lia | hproj; lia | hproj; assumption
        | hproj; first [assumption | reflexivity] | hproj; rewrite Hst; exact Hfr | unfold h_used; hproj; lia
        | hproj; assumption | hproj; assumption | unfold h_used; hproj; lia | hproj; lia | counts Hst ].
      * unfold ybuf_chk_fail.
        rewrite (ybs_set_eq (h_set_decbuf (h_set_lex_off h lx off) db) _ rest _
                   ltac:(hproj; exact Hst) ltac:(unfold h_used; hproj; lia)). cbn.
        weak_tac2 Hst.
      * unfold ybuf_chk_fail.
        rewrite (ybs_set_eq (h_set_decbuf (h_set_lex_off h lx off) db) _ rest _
                   ltac:(hproj; exact Hst) ltac:(unfold h_used; hproj; lia)). cbn.
        weak_tac2 Hst.
  - (* [comment removed for export] *)
    lexstep HLEX.
    pose proof (count_array_nonneg rest) as Hcr.
    assert (Hal : 0 < cx_arrayLevel cx) by (rewrite Ha; cbn [count_array is_array_state]; lia).
    destruct tok; try contradiction; unfold yparse_error.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) mkpre len off0 h lx off Hst.
      eapply set_frame_again; try (hproj; first [exact Hst | exact Hfr | reflexivity | exact HP]); cbn; auto.
    + (* [comment removed for export] *) leaf_done. tauto.
    + (* [comment removed for export] *) leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) cbn [cb_end_array jf_callbacks ybind yassert].
      destruct (Z.ltb_spec 0 (cx_arrayLevel cx)); [|lia]. cbn [ybind].
      mkpre len off0 h lx off Hst.
      eapply pop_again; [hproj; exact Hst | exact Hfr | reflexivity | exact HP | counts Hst | counts Hst].
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
  - (* [comment removed for export] *)
    lexstep HLEX.
    destruct tok; try contradiction; unfold yparse_error.
    + (* [comment removed for export] *) cbn [cb_boolean jf_callbacks ybind]. go_value Hst Hfr.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) leaf_done. tauto.
    + (* [comment removed for export] *) leaf_error Hst.
    + (* [comment removed for export] *) cbn [cb_start_array jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_start_map jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_null jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *)
      rewrite (ybs_current_eq (h_set_lex_off h lx off) _ rest ltac:(hproj; exact Hst)).
      cbn [ybind state_eqb state_code Z.eqb Pos.eqb]. unfold yparse_error.
      mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) mkpre len off0 h lx off Hst. leaf_error Hst.
    + (* [comment removed for export] *) cbn [cb_number jf_callbacks ybind]. unfold yassert.
      destruct (Z.ltb_spec 0 n); [|exfalso; destruct Htok as (_&_&(?&?&?&?&?&?&?)); lia]. cbn [ybind].
      go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_number jf_callbacks ybind]. unfold yassert.
      destruct (Z.ltb_spec 0 n); [|exfalso; destruct Htok as (_&_&(?&?&?&?&?&?&?)); lia]. cbn [ybind].
      go_value Hst Hfr.
    + (* [comment removed for export] *) cbn [cb_string jf_callbacks ybind]. go_value Hst Hfr.
    + (* [comment removed for export] *)
      destruct Htok as (Hlx' & Hprog & (i & Hob & Hi & Hn & Hin & H1 & Hq1 & Hq2 & Hend & Hbody)).
      subst ob. cbn [out_bytes].
      eapply ypost_bind.
      { apply (ydecode_tok_post (h_set_lex_off h lx off) (zslice txt i n) n); hproj; auto; try lia.
        apply sbody_ix_slice; auto; lia. }
      intros h1 (db & -> & Hdbi & Hdbu). unfold ybuf_err. hproj.
      destruct (yb_state db) eqn:Hdbs'; cbn [buf_state_ok negb].
      * unfold ybuf_data_chk, ybuf_len_chk. rewrite Hdbs'. cbn [ybind cb_string jf_callbacks].
        eapply ygot_value_post;
        [ hproj; exact Hst | s_member | hproj; tauto | hproj; lia | hproj; lia | hproj; assumption
        | hproj; first [assumption | reflexivity] | hproj; rewrite Hst; exact Hfr | unfold h_used; hproj; lia
        | hproj; assumption | hproj; assumption | unfold h_used; hproj; lia | hproj; lia | counts Hst ].
      * unfold ybuf_chk_fail.
        rewrite (ybs_set_eq (h_set_decbuf (h_set_lex_off h lx off) db) _ rest _
                   ltac:(hproj; exact Hst) ltac:(unfold h_used; hproj; lia)). cbn.
        weak_tac2 Hst.
      * unfold ybuf_chk_fail.
        rewrite (ybs_set_eq (h_set_decbuf (h_set_lex_off h lx off) db) _ rest _
                   ltac:(hproj; exact Hst) ltac:(unfold h_used; hproj; lia)). cbn.
        weak_tac2 Hst.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition loop_pre (len : Z) (h : yhandle) (cx : yctx) : Prop :=
  hinv len h cx \/
  (weak_inv len h /\ exists s rest, h_stack h = s :: rest /\ is_error_state s = true).

(* [comment removed for export] *)
Definition passes_left (len : Z) (h : yhandle) : Z :=
  match h_stack h with
  | s :: _ => if is_error_state s then 1 else len - h_bytesConsumed h + 2
  | [] => 0
  end.

Theorem yparse_loop_post : forall txt len fuel h cx,
  len = zlength txt -> len < 2^32 -> loop_pre len h cx ->
  passes_left len h <= Z.of_nat fuel ->
  ypost (yparse_loop jf_callbacks txt len fuel h cx)
        (fun r => let '(st, h', cx') := r in weak_inv len h').
Proof.
  intros txt len fuel. induction fuel as [|fuel IH]; intros h cx Hlen H32 Hpre Hfuel.
  - exfalso. unfold passes_left in Hfuel. destruct Hpre as [Hinv|(Hw & s & rest & Hst & He)].
    + destruct Hinv as (_ & Hoff & _ & _ & (Hfr & _) & _ & _).
      destruct (h_stack h) as [|s rest]; [contradiction|].
      rewrite (frames_ok_not_error _ _ Hfr) in Hfuel. cbn in Hfuel. lia.
    + rewrite Hst, He in Hfuel. cbn in Hfuel. lia.
  - cbn [yparse_loop]. destruct Hpre as [Hinv|(Hw & s & rest & Hst & He)].
    + eapply ypost_bind. { apply yparse_step_post; eauto. }
      intros [st h1 cx1|h1 cx1]; cbn -[Z.add Z.sub].
      * auto.
      * intros Hstep. apply IH; auto.
        -- destruct Hstep as [[Hinv1 _]|Herr]; [left|right]; auto.
        -- (* [comment removed for export] *)
          unfold passes_left in *.
          destruct Hinv as (_ & Hoff & _ & _ & (Hfr & _) & _ & _).
          destruct (h_stack h) as [|s rest]; [contradiction|].
          rewrite (frames_ok_not_error _ _ Hfr) in Hfuel.
          destruct Hstep as [[Hinv1 Hprog]|(Hw1 & s1 & rest1 & Hst1 & He1)].
          ++ destruct Hinv1 as (_ & Hoff1 & _ & _ & (Hfr1 & _) & _ & _).
             destruct (h_stack h1) as [|s1 rest1]; [contradiction|].
             rewrite (frames_ok_not_error _ _ Hfr1). lia.
          ++ rewrite Hst1, He1. lia.
    + (* [comment removed for export] *)
      unfold yparse_step. rewrite (ybs_current_eq h s rest Hst). cbn [ybind].
      destruct s; try discriminate; cbn; exact Hw.
Qed.

Theorem ydo_parse_post : forall txt len h cx,
  len = zlength txt -> len < 2^32 -> hinv len (h_set_off h 0) cx ->
  ypost (ydo_parse jf_callbacks txt len h cx)
        (fun r => let '(st, h', cx') := r in weak_inv len h').
Proof.
  intros txt len h cx Hlen H32 Hinv. unfold ydo_parse.
  apply yparse_loop_post; auto.
  - left; auto.
  - unfold passes_left, parse_fuel. destruct Hinv as (_ & Hoff & _ & _ & (Hfr & _) & _ & _).
    cbn [h_stack h_set_off h_bytesConsumed] in *.
    destruct (h_stack h) as [|s rest]; [contradiction|].
    rewrite (frames_ok_not_error _ _ Hfr). rewrite !Nat2Z.inj_succ, Z2Nat.id; lia.
Qed.

Corollary ydo_parse_safe : forall txt len h cx,
  len = zlength txt -> len < 2^32 -> hinv len (h_set_off h 0) cx ->
  ysafe (ydo_parse jf_callbacks txt len h cx).
Proof. intros. eapply ypost_safe. apply ydo_parse_post; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem yajl_alloc_post : forall len, 0 <= len ->
  ypost (yajl_alloc 1 1)
        (fun r => match r with
                  | None => True
                  | Some h => hinv len (h_set_off h 0) (mkCtx 0 0) /\ h_bytesConsumed h = 0 /\
                              h_stack h = [ST_start] /\ h_stack_size h = YAJL_BS_INC /\
                              h_decbuf h = ybuf_zero /\ lx_buf (h_lexer h) = ybuf_zero /\
                              lx_error (h_lexer h) = LE_ok /\ h_parseError h = None
                  end).
Proof.
  intros len Hlen. unfold yajl_alloc.
  eapply ypost_bind. { apply ypost_ymalloc. intros r; exact I. }
  intros [hb|] _; cbv beta iota; [|exact I].
  eapply ypost_bind. { apply ylex_alloc_post with (Q := fun r => match r with None => True | Some (blk, lx) => lex_inv lx /\ lx_error lx = LE_ok end); auto. }
  intros [[lb lx]|]; cbv beta iota.
  - intros [Hlx Herr]. cbn -[ylex_free]. intros [db|]; cbn -[ylex_free].
    + intros [sb|]; cbn -[ylex_free].
      * unfold hinv, stack_inv, h_used; cbn. destruct Hlx as (?&?&?&?&?&?&Hb).
        repeat match goal with |- _ /\ _ => split end; auto; try lia.
        -- unfold lex_inv; repeat match goal with |- _ /\ _ => split end; auto.
        -- apply buf_inv_zero.
        -- unfold zlength; cbn. unfold YAJL_BS_INC. lia.
        -- congruence.
        -- exists 1. unfold YAJL_BS_INC. lia.
      * pose proof (ylex_free_safe lb lx) as Hs. apply ypost_true in Hs.
        eapply ypost_bind; [exact Hs|]. intros; cbn. exact I.
    + pose proof (ylex_free_safe lb lx) as Hs. apply ypost_true in Hs.
      eapply ypost_bind; [exact Hs|]. intros; cbn. exact I.
  - intros _. cbn. exact I.
Qed.

Lemma yajl_free_safe : forall h, ysafe (yajl_free h).
Proof.
  intros h. unfold yajl_free. apply (ypost_safe _ (fun _ => True)).
  eapply ypost_bind with (Q := fun _ => True).
  { destruct (h_stack_blk h); cbn; auto. }
  intros _ _. eapply ypost_bind with (Q := fun _ => True).
  { apply ypost_true, ybuf_free_safe. }
  intros _ _. eapply ypost_bind with (Q := fun _ => True).
  { apply ypost_true, ylex_free_safe. }
  intros _ _. cbn. exact I.
Qed.

(* [comment removed for export] *)
Theorem yfuzz_one_post : forall data size (post : ystatus -> yhandle -> yctx -> yprog unit),
  size = zlength data -> size < 2^32 ->
  (forall st h cx, weak_inv size h -> ypost (post st h cx) (fun _ => True)) ->
  ypost (yfuzz_one jf_callbacks post data size) (fun rc => rc = 0).
Proof.
  intros data size post Hsz H32 Hpost. unfold yfuzz_one.
  eapply ypost_bind. { apply (yajl_alloc_post size). subst; apply zlength_nonneg. }
  intros [h|]; cbn.
  - intros (Hinv & _). eapply ypost_bind. { apply ydo_parse_post; eauto. }
    intros [[st h1] cx1] Hw. eapply ypost_bind. { apply Hpost; eauto. }
    intros _ _. eapply ypost_bind with (Q := fun _ => True). { apply ypost_true, yajl_free_safe. }
    intros _ _. cbn. reflexivity.
  - intros _. reflexivity.
Qed.

Corollary yLLVMFuzzerTestOneInput_post : forall data size,
  size = zlength data -> size < 2^32 ->
  ypost (yLLVMFuzzerTestOneInput data size) (fun rc => rc = 0).
Proof.
  intros. unfold yLLVMFuzzerTestOneInput. apply yfuzz_one_post; auto. intros; cbn; exact I.
Qed.

Lemma yrun_calls_post : forall n payload payload_len rc0,
  payload_len = zlength payload -> payload_len < 2^32 -> rc0 = 0 ->
  ypost (yrun_calls yLLVMFuzzerTestOneInput n payload payload_len rc0) (fun rc => rc = 0).
Proof.
  induction n as [|n IH]; intros payload payload_len rc0 Hpl H32 Hrc; cbn [yrun_calls].
  - exact Hrc.
  - eapply ypost_bind. { apply yLLVMFuzzerTestOneInput_post; auto. }
    intros rc1 ->. cbn. apply IH; auto.
Qed.

Theorem ytarget_run_post : forall config config_len payload payload_len,
  payload_len = zlength payload -> payload_len < 2^32 ->
  ypost (ytarget_run config config_len payload payload_len) (fun rc => rc = 0 \/ rc = 2).
Proof.
  intros config config_len payload payload_len Hpl H32. unfold ytarget_run, ytarget_run_with.
  eapply ypost_bind with (Q := fun _ => True).
  { destruct (payload_len =? 0); cbn; auto. intros r; destruct r; cbn; auto. }
  intros [own|] _; cbv beta iota; [|cbn; auto].
  eapply ypost_bind. { apply yrun_calls_post; auto. }
  intros rc ->. cbn. left; reflexivity.
Qed.

(* [comment removed for export] *)
Corollary ytarget_run_safe : forall config config_len payload payload_len,
  payload_len = zlength payload -> payload_len < 2^32 ->
  ysafe (ytarget_run config config_len payload payload_len).
Proof. intros. eapply ypost_safe. apply ytarget_run_post; auto. Qed.
