(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateCalleeSpec2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInffastGen.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefItableGen.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeFCw.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeFR.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_BAD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_TERM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_LIT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_TYPE.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_LENGTH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_DICT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_CHECK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_COPY.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_STORED.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_HDR.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_HEAD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_LENEXT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_MATCH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_LEN.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_TABLE.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_LENLENS.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_CODELENS1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)

Section Arms.

  (* [comment removed for export] *)
  Definition codelens_chain (flush : Z) (w : iw) : bool :=
    codelens_okb w && match codelens_next flush w with Some w2 => len__chain w2 | None => true end.
  (* [comment removed for export] *)
  Definition lenlens_chain (flush : Z) (w : iw) : bool :=
    lenlens_okb w && match lenlens_next w with Some w2 => codelens_chain flush w2 | None => true end.
  (* [comment removed for export] *)
  Definition table_chain (flush : Z) (w : iw) : bool :=
    match table_next w with Some w2 => lenlens_chain flush w2 | None => true end.

  (* [comment removed for export] *)
  Definition okL (flush : Z) (w : iw) : bool :=
    let s := w_s w in let m := is_mode s in
    if (m =? DICT) || (m =? MEM) || (m =? SYNC) then true
    else leave_okb s &&
      (if m =? DISTEXT then distext_chain w
       else if m =? DIST then dist_chain w
       else if m =? LENEXT then lenext_chain w
       else if m =? MATCH then match_okb s
       else if m =? LEN then len_chain w
       else if m =? LEN_ then len__chain w
       else if m =? TABLE then table_chain flush w
       else if m =? LENLENS then lenlens_chain flush w
       else if m =? CODELENS then codelens_chain flush w
       else true).
  Local Ltac xe_leaf := split; [assumption | repeat (split; [first [assumption | reflexivity] |]); first [assumption | reflexivity]].
  (* [comment removed for export] *)
  Local Ltac okL_at H Hm := unfold okL in H; cbn [w_s w_c w_r] in H; rewrite Hm in H; cbn -[leave_okb distext_chain dist_chain lenext_chain match_okb len_chain len__chain table_chain lenlens_chain codelens_chain iset_mode] in H.
  Local Ltac ok_leave := intros flush w Hm H; okL_at H Hm; first [exact H | apply andb_prop in H; exact (proj1 H)].
  Local Ltac ok_both := intros flush w Hm H; okL_at H Hm; apply andb_prop in H; exact H.

  (* [comment removed for export] *)
  Lemma okL_plain : forall flush s c r m,
    is_mode s = m ->
    In m [HEAD; FLAGS; TIME; OS; EXLEN; EXTRA; NAME; COMMENT; HCRC; DICTID; TYPE; TYPEDO; STORED; COPY_; COPY; LIT; CHECK; LENGTH; DONE; BAD] ->
    okL flush (mkW s c r) = leave_okb s.
  Proof.
    intros flush s c r m Hm Hin. unfold okL. cbn [w_s w_c w_r]. rewrite Hm. cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn -[leave_okb]; apply Bool.andb_true_r|]). destruct Hin.
  Qed.
  Local Ltac inm := cbn; repeat (first [left; reflexivity | right]).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma okL_carry : forall flush s c r s' c' r' m m',
    is_mode s = m -> okL flush (mkW s c r) = true ->
    In m [HEAD; FLAGS; TIME; OS; EXLEN; EXTRA; NAME; COMMENT; HCRC; DICTID; TYPE; TYPEDO; STORED; COPY_; COPY; LIT; CHECK; LENGTH; DONE; BAD] ->
    is_mode s' = m' ->
    In m' [HEAD; FLAGS; TIME; OS; EXLEN; EXTRA; NAME; COMMENT; HCRC; DICTID; TYPE; TYPEDO; STORED; COPY_; COPY; LIT; CHECK; LENGTH; DONE; BAD] ->
    is_wrap s' = is_wrap s -> is_flags s' = is_flags s -> is_check s' = is_check s ->
    okL flush (mkW s' c' r') = true.
  Proof.
    intros flush s c r s' c' r' m m' Hm H Hin Hm' Hin' E1 E2 E3.
    rewrite (okL_plain flush s c r m Hm Hin) in H. rewrite (okL_plain flush s' c' r' m' Hm' Hin').
    unfold leave_okb in *. rewrite E1, E2, E3. exact H.
  Qed.
  Lemma hcrc_on_flags : forall s, hcrc_on s = true -> (is_flags s =? 0) = false.
  Proof.
    intros s H. unfold hcrc_on in H. apply andb_prop in H. destruct H as [H _].
    apply Z.eqb_neq. intros E. rewrite E in H. discriminate H.
  Qed.

  (* [comment removed for export] *)
  Lemma okL_hcrc : forall flush s s' c' r' m', hcrc_on s = true -> is_mode s' = m' ->
    In m' [HEAD; FLAGS; TIME; OS; EXLEN; EXTRA; NAME; COMMENT; HCRC; DICTID; TYPE; TYPEDO; STORED; COPY_; COPY; LIT; CHECK; LENGTH; DONE; BAD] ->
    is_flags s' = is_flags s -> okL flush (mkW s' c' r') = true.
  Proof.
    intros flush s s' c' r' m' Hon Hm' Hin' E2. rewrite (okL_plain flush s' c' r' m' Hm' Hin').
    unfold leave_okb. rewrite E2, (hcrc_on_flags s Hon). cbn [negb]. rewrite Bool.orb_true_r. reflexivity.
  Qed.
  Local Ltac carry m m' := intros; eapply (okL_carry _ _ _ _ _ _ _ m m'); [eassumption | eassumption | inm | reflexivity | inm | reflexivity | reflexivity | reflexivity].
  Local Ltac hcarry m' := intros; eapply (okL_hcrc _ _ _ _ _ m'); [eassumption | reflexivity | inm | reflexivity].

  (* [comment removed for export] *)

  Local Ltac okL_goal m := unfold okL; cbn [w_s w_c w_r]; rewrite m; cbn -[leave_okb distext_chain dist_chain lenext_chain match_okb len_chain len__chain table_chain lenlens_chain codelens_chain iset_mode].

  (* [comment removed for export] *)

End Arms.
