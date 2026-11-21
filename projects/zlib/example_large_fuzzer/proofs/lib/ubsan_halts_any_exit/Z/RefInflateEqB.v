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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflate_runA.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCalleeSpec2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeS1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeS2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeFR.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeTY.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateEqD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateEqF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateEqS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma match_copy_len : forall win ob put from copy,
  arr_len (fst (fst (fst (match_copy win (ob, put, from, copy))))) = arr_len ob.
Proof.
  intros. unfold match_copy. cbn [snd].
  apply (loopZ_ind (fun st : arr * Z * fromptr * Z => arr_len (fst (fst (fst st))) = arr_len ob)); [|reflexivity].
  intros [[[o p] f] c] H. cbn [fst snd] in *. rewrite arr_len_set. exact H.
Qed.

Section Frame.
  Variable NO : Z.
Variable T0 : Z.
Variable O0 : Z.

  Definition FP (w : iw) : Prop :=
    arr_len (ic_outbuf (w_c w)) = NO /\ ic_total_out (w_c w) = T0 /\ ir_out (w_r w) = O0
    /\ is_mode (w_s w) <> MEM /\ is_mode (w_s w) <> SYNC.

  Definition RETOK (rc : Z) (w : iw) : Prop := rc = Z_NEED_DICT /\ ic_next_out (w_c w) = ir_put (w_r w).
  Definition FPr {A} (res : ares A) : Prop :=
    match res with ARun _ w => FP w | ALeave w => FP w | ARet rc w => FP w /\ RETOK rc w end.

  Section Rules.
    Context {A B : Type}.
    Lemma FPr_bind : forall (m : AM A) (f : A -> AM B) w,
      FPr (m w) -> (forall a w', FP w' -> FPr (f a w')) -> FPr (abind m f w).
    Proof. intros m f w Hm Hf. unfold abind. destruct (m w) as [a w'|w'|rc w']; [exact (Hf a w' Hm) | exact Hm | exact Hm]. Qed.
    Lemma FPr_bind_run : forall (m : AM A) (f : A -> AM B) w a w',
      m w = ARun a w' -> FPr (f a w') -> FPr (abind m f w).
    Proof. intros m f w a w' E H. unfold abind. rewrite E. exact H. Qed.
  End Rules.

  Lemma restore_fp : forall w, FP w -> FPr (amodify RESTORE w).
  Proof. intros [s c r] (F1 & F2 & F3 & F4 & F5). unfold FPr, amodify, RESTORE, FP. cbn [w_s w_c w_r] in *. sacc. repeat split; assumption. Qed.

  Lemma fast_fp : forall w, is_mode (w_s w) = LEN -> FP w -> FPr (amodify (fun w0 => LOAD (inflate_fast (RESTORE w0))) w).
  Proof.
    intros [s c r] E (F1 & F2 & F3 & F4 & F5). cbn [w_s w_c w_r] in *. unfold FPr, amodify, RESTORE. cbn [w_s w_c w_r].
    match goal with |- context [inflate_fast (mkW ?a ?b ?d)] =>
      pose proof (inflate_fast_frame_proof a b d) as FR; cbv zeta in FR; destruct FR as (_ & FRL & _); revert FRL;
      rewrite (inflate_fast_eqo a b d); pose proof (ff_loopo_mode a b d) as HM; destruct (ff_loopo a b d) as [f mm] end.
    cbn [snd] in HM. unfold ff_posto, LOAD. cbv zeta.
    destruct mm as [[md [mg|]]|]; cbn [w_s w_c w_r]; unfold wset_r, FP; cbn [w_s w_c w_r]; sacc; rewrite F1; intros FRL.
    - destruct HM as [-> | ->]; (repeat split; [exact FRL | exact F2 | exact F3 | discriminate | discriminate]).
    - destruct HM as [-> | ->]; (repeat split; [exact FRL | exact F2 | exact F3 | discriminate | discriminate]).
    - repeat split; [exact FRL | exact F2 | exact F3 | exact F4 | exact F5].
  Qed.

  Ltac fp_state :=
    first [ assumption
          | unfold FP; cbn [w_s w_c w_r wset_s wset_c wset_r RESTORE]; unfold fixedtables; sacc; rewrite ?arr_len_set, ?arr_len_blit;
            repeat match goal with |- _ /\ _ => split end;
            first [ assumption | reflexivity | (intros XX; cbv in XX; discriminate XX)
                  | match goal with H : is_mode ?s = _ |- is_mode ?s <> _ => rewrite H; intros XX; cbv in XX; discriminate XX end
                  | match goal with |- (if ?b then _ else _) <> _ => destruct b; intros XX; cbv in XX; discriminate XX end ] ].

  Create HintDb fp discriminated.

  Ltac fp_step :=
    cbv beta zeta;
    lazymatch goal with
    | |- forall a w, FP w -> _ => intros ? ? (?&?&?&?&?)
    | |- FPr (ARun _ _) => unfold FPr; fp_state
    | |- FPr (ALeave _) => unfold FPr; fp_state
    | |- FPr (ARet _ _) => unfold FPr; split; [fp_state | split; [reflexivity | cbn [w_c w_r wset_s wset_c wset_r RESTORE]; sacc; reflexivity]]
    | |- FPr (abind (gs _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FPr (abind (gr _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FPr (abind (gc _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FPr (abind aget _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FPr (abind (BITS _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FPr (abind HOLD _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FPr (abind (us _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FPr (abind (uc _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FPr (abind (ur _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FPr (abind (amodify RESTORE) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FPr (abind _ _ _) => apply FPr_bind; [|]
    | |- FPr ((if ?b then _ else _) _) => destruct b
    | |- FPr (if ?b then _ else _) => destruct b
    | |- FPr (match match_copy ?wn ?st with _ => _ end) =>
        let ML := fresh "ML" in let ob := fresh "ob" in
        pose proof (match_copy_len wn (fst (fst (fst st))) (snd (fst (fst st))) (snd (fst st)) (snd st)) as ML;
        cbn [fst snd] in ML; destruct (match_copy wn st) as [[[ob ?] ?] ?];
        cbn [fst w_s w_c w_r wset_s wset_c wset_r] in ML; sacc_in ML; rewrite ?arr_len_set, ?arr_len_blit in ML;
        let LL := fresh "LL" in assert (LL : arr_len ob = NO) by (rewrite ML; assumption); clear ML
    | |- FPr ((match ?x with _ => _ end) _) => destruct x
    | |- FPr (match ?x with _ => _ end) => destruct x
    | |- FPr (amodify RESTORE _) => apply restore_fp; fp_state
    | |- FPr (amodify _ _) => apply fast_fp; [cbn [w_s wset_s wset_c wset_r]; sacc; first [assumption | reflexivity] | fp_state]
    | |- FPr _ =>
        first [ solve [eauto 3 with fp nocore]
              | progress (cbv beta zeta delta [aret aleave areturn aget agets gs gc gr us uc ur BITS HOLD DROPBITS INITBITS BYTEBITS
                                              set_mode set_msg go_bad set_adler_check CRC2 CRC4 aux set_back add_back set_lens
                                              PULLBYTE crc_input NEEDBITS DECODE1 DECODE2]) ]
    end.
  Ltac fp := repeat fp_step.

  Hint Extern 1 (FP _) => fp_state : fp.

  Lemma NEEDBITS_k_fp : forall k n w, FP w -> FPr (NEEDBITS_k k n w).
  Proof. induction k as [|k IH]; intros n w (F1 & F2 & F3 & F4 & F5); cbn [NEEDBITS_k]; fp. Qed.
  Lemma NEEDBITS_fp : forall n w, FP w -> FPr (NEEDBITS n w).
  Proof. intros n w HF. unfold NEEDBITS. apply NEEDBITS_k_fp. exact HF. Qed.
  Hint Resolve NEEDBITS_fp : fp.

  Lemma DECODE_k_fp : forall k p index need w, FP w -> FPr (DECODE_k k p index need w).
  Proof. induction k as [|k IH]; intros p index need w (F1 & F2 & F3 & F4 & F5); cbn [DECODE_k]; fp. Qed.
  Lemma DECODE1_fp : forall p n w, FP w -> FPr (DECODE1 p n w).
  Proof. intros p n w HF. unfold DECODE1. apply DECODE_k_fp. exact HF. Qed.
  Lemma DECODE2_fp : forall p l w, FP w -> FPr (DECODE2 p l w).
  Proof. intros p l w HF. unfold DECODE2. apply DECODE_k_fp. exact HF. Qed.
  Hint Resolve DECODE1_fp DECODE2_fp : fp.

  Lemma lens_repeat_fp : forall copy len w, FP w -> FPr (lens_repeat copy len w).
  Proof.
    intros copy len [s c r] (F1 & F2 & F3 & F4 & F5). unfold lens_repeat, us, FPr. cbn [w_s w_c w_r wset_s].
    lazymatch goal with |- context [loopZ ?n ?st ?a] => destruct (loopZ n st a) as [[l h] cp] end.
    unfold FP. cbn [w_s w_c w_r]. sacc. repeat split; assumption.
  Qed.
  Hint Resolve lens_repeat_fp : fp.

  Lemma arm_DONE_fp : forall w, FP w -> FPr (arm_DONE w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_DONE. fp. Qed.
  Hint Resolve arm_DONE_fp : fp.
  Lemma arm_LENGTH_fp : forall w, FP w -> FPr (arm_LENGTH w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_LENGTH. fp. Qed.
  Hint Resolve arm_LENGTH_fp : fp.
  Lemma arm_BAD_fp : forall w, FP w -> FPr (arm_BAD w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_BAD. fp. Qed.
  Hint Resolve arm_BAD_fp : fp.
  Lemma arm_LIT_fp : forall w, FP w -> FPr (arm_LIT w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_LIT. fp. Qed.
  Hint Resolve arm_LIT_fp : fp.
  Lemma arm_MATCH_fp : forall iv w, FP w -> FPr (arm_MATCH iv w).
  Proof. intros iv w (F1 & F2 & F3 & F4 & F5). unfold arm_MATCH. fp. Qed.
  Hint Resolve arm_MATCH_fp : fp.
  Lemma arm_DISTEXT_fp : forall iv w, FP w -> FPr (arm_DISTEXT iv w).
  Proof. intros iv w (F1 & F2 & F3 & F4 & F5). unfold arm_DISTEXT. fp. Qed.
  Hint Resolve arm_DISTEXT_fp : fp.
  Lemma arm_DIST_fp : forall iv w, FP w -> FPr (arm_DIST iv w).
  Proof. intros iv w (F1 & F2 & F3 & F4 & F5). unfold arm_DIST. fp. Qed.
  Hint Resolve arm_DIST_fp : fp.
  Lemma arm_LENEXT_fp : forall iv w, FP w -> FPr (arm_LENEXT iv w).
  Proof. intros iv w (F1 & F2 & F3 & F4 & F5). unfold arm_LENEXT. fp. Qed.
  Hint Resolve arm_LENEXT_fp : fp.
  Lemma arm_LEN_fp : forall iv w, is_mode (w_s w) = LEN -> FP w -> FPr (arm_LEN iv w).
  Proof. intros iv w E (F1 & F2 & F3 & F4 & F5). unfold arm_LEN. fp. Qed.
  Hint Resolve arm_LEN_fp : fp.
  Lemma arm_LEN__fp : forall iv w, FP w -> FPr (arm_LEN_ iv w).
  Proof. intros iv w (F1 & F2 & F3 & F4 & F5). unfold arm_LEN_, set_mode. eapply FPr_bind_run; [reflexivity|]. apply arm_LEN_fp; [reflexivity|fp_state]. Qed.
  Hint Resolve arm_LEN__fp : fp.
  Lemma codelens_body_fp : forall w, FP w -> FPr (codelens_body w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold codelens_body. fp. Qed.
  Hint Resolve codelens_body_fp : fp.
  Lemma codelens_while_fp : forall k w, FP w -> FPr (codelens_while k w).
  Proof. induction k as [|k IH]; intros w (F1 & F2 & F3 & F4 & F5); cbn [codelens_while]; fp. Qed.
  Hint Resolve codelens_while_fp : fp.
  Lemma arm_CODELENS_fp : forall iv flush w, FP w -> FPr (arm_CODELENS iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4 & F5). unfold arm_CODELENS. fp. Qed.
  Hint Resolve arm_CODELENS_fp : fp.
  Lemma lenlens_while1_fp : forall k w, FP w -> FPr (lenlens_while1 k w).
  Proof. induction k as [|k IH]; intros w (F1 & F2 & F3 & F4 & F5); cbn [lenlens_while1]; fp. Qed.
  Hint Resolve lenlens_while1_fp : fp.
  Lemma lenlens_while2_fp : forall k w, FP w -> FPr (lenlens_while2 k w).
  Proof. induction k as [|k IH]; intros w (F1 & F2 & F3 & F4 & F5); cbn [lenlens_while2]; fp. Qed.
  Hint Resolve lenlens_while2_fp : fp.
  Lemma arm_LENLENS_fp : forall iv flush w, FP w -> FPr (arm_LENLENS iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4 & F5). unfold arm_LENLENS. fp. Qed.
  Hint Resolve arm_LENLENS_fp : fp.
  Lemma arm_TABLE_fp : forall iv flush w, FP w -> FPr (arm_TABLE iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4 & F5). unfold arm_TABLE. fp. Qed.
  Hint Resolve arm_TABLE_fp : fp.
  Lemma arm_COPY_fp : forall w, FP w -> FPr (arm_COPY w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_COPY. fp. Qed.
  Hint Resolve arm_COPY_fp : fp.
  Lemma arm_COPY__fp : forall w, FP w -> FPr (arm_COPY_ w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_COPY_. fp. Qed.
  Hint Resolve arm_COPY__fp : fp.
  Lemma arm_STORED_fp : forall iv flush w, FP w -> FPr (arm_STORED iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4 & F5). unfold arm_STORED. fp. Qed.
  Hint Resolve arm_STORED_fp : fp.
  Lemma arm_TYPEDO_fp : forall iv flush w, FP w -> FPr (arm_TYPEDO iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4 & F5). unfold arm_TYPEDO. fp. Qed.
  Hint Resolve arm_TYPEDO_fp : fp.
  Lemma arm_TYPE_fp : forall iv flush w, FP w -> FPr (arm_TYPE iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4 & F5). unfold arm_TYPE. fp. Qed.
  Hint Resolve arm_TYPE_fp : fp.
  Lemma arm_DICT_fp : forall iv flush w, FP w -> FPr (arm_DICT iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4 & F5). unfold arm_DICT. fp. Qed.
  Hint Resolve arm_DICT_fp : fp.
  Lemma arm_DICTID_fp : forall iv flush w, FP w -> FPr (arm_DICTID iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4 & F5). unfold arm_DICTID. fp. Qed.
  Hint Resolve arm_DICTID_fp : fp.
  Lemma arm_HCRC_fp : forall w, FP w -> FPr (arm_HCRC w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_HCRC. fp. Qed.
  Hint Resolve arm_HCRC_fp : fp.
  Lemma name_like_fp : forall fl w, FP w -> FPr (name_like fl w).
  Proof. intros fl w (F1 & F2 & F3 & F4 & F5). unfold name_like. fp. Qed.
  Hint Resolve name_like_fp : fp.
  Lemma arm_COMMENT_fp : forall w, FP w -> FPr (arm_COMMENT w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_COMMENT. fp. Qed.
  Hint Resolve arm_COMMENT_fp : fp.
  Lemma arm_NAME_fp : forall w, FP w -> FPr (arm_NAME w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_NAME. fp. Qed.
  Hint Resolve arm_NAME_fp : fp.
  Lemma arm_EXTRA_fp : forall w, FP w -> FPr (arm_EXTRA w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_EXTRA. fp. Qed.
  Hint Resolve arm_EXTRA_fp : fp.
  Lemma arm_EXLEN_fp : forall w, FP w -> FPr (arm_EXLEN w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_EXLEN. fp. Qed.
  Hint Resolve arm_EXLEN_fp : fp.
  Lemma arm_OS_fp : forall w, FP w -> FPr (arm_OS w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_OS. fp. Qed.
  Hint Resolve arm_OS_fp : fp.
  Lemma arm_TIME_fp : forall w, FP w -> FPr (arm_TIME w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_TIME. fp. Qed.
  Hint Resolve arm_TIME_fp : fp.
  Lemma arm_FLAGS_fp : forall w, FP w -> FPr (arm_FLAGS w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5). unfold arm_FLAGS. fp. Qed.
  Hint Resolve arm_FLAGS_fp : fp.
  Lemma arm_HEAD_fp : forall iv w, FP w -> FPr (arm_HEAD iv w).
  Proof. intros iv w (F1 & F2 & F3 & F4 & F5). unfold arm_HEAD. fp. Qed.
  Hint Resolve arm_HEAD_fp : fp.
End Frame.

Section FrameB.
  Variable NO : Z.
Variable TOT0 : Z.

  Definition cmodes (m : Z) : Prop := m = CHECK \/ m = LENGTH \/ m = DONE \/ m = BAD.
  Definition FPB (w : iw) : Prop :=
    arr_len (ic_outbuf (w_c w)) = NO /\ ic_total_out (w_c w) = wrap64 (TOT0 + ir_put (w_r w)) /\ ir_out (w_r w) = ir_left (w_r w)
    /\ is_mode (w_s w) <> MEM /\ is_mode (w_s w) <> SYNC /\ cmodes (is_mode (w_s w)).
  Definition FPBr {A} (res : ares A) : Prop :=
    match res with ARun _ w => FPB w | ALeave w => FPB w | ARet rc w => FPB w /\ RETOK rc w end.

  Section Rules.
    Context {A B : Type}.
    Lemma FPBr_bind : forall (m : AM A) (f : A -> AM B) w,
      FPBr (m w) -> (forall a w', FPB w' -> FPBr (f a w')) -> FPBr (abind m f w).
    Proof. intros m f w Hm Hf. unfold abind. destruct (m w) as [a w'|w'|rc w']; [exact (Hf a w' Hm) | exact Hm | exact Hm]. Qed.
    Lemma FPBr_bind_run : forall (m : AM A) (f : A -> AM B) w a w',
      m w = ARun a w' -> FPBr (f a w') -> FPBr (abind m f w).
    Proof. intros m f w a w' E H. unfold abind. rewrite E. exact H. Qed.
  End Rules.

  Ltac fpb_state :=
    first [ assumption
          | unfold FPB; cbn [w_s w_c w_r wset_s wset_c wset_r RESTORE]; unfold fixedtables; sacc; rewrite ?arr_len_set, ?arr_len_blit;
            repeat match goal with |- _ /\ _ => split end;
            first [ assumption | reflexivity | (intros XX; cbv in XX; discriminate XX)
                  | match goal with H : is_mode ?s = _ |- is_mode ?s <> _ => rewrite H; intros XX; cbv in XX; discriminate XX end
                  | match goal with |- (if ?b then _ else _) <> _ => destruct b; intros XX; cbv in XX; discriminate XX end
                  | (unfold cmodes; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity | right; right; right; reflexivity]) ] ].
  Create HintDb fpb discriminated.
  Ltac fpb_step :=
    cbv beta zeta;
    lazymatch goal with
    | |- forall a w, FPB w -> _ => intros ? ? (?&?&?&?&?&?)
    | |- FPBr (ARun _ _) => unfold FPBr; fpb_state
    | |- FPBr (ALeave _) => unfold FPBr; fpb_state
    | |- FPBr (abind (gs _) _ _) => eapply FPBr_bind_run; [reflexivity|]
    | |- FPBr (abind (gr _) _ _) => eapply FPBr_bind_run; [reflexivity|]
    | |- FPBr (abind (gc _) _ _) => eapply FPBr_bind_run; [reflexivity|]
    | |- FPBr (abind aget _ _) => eapply FPBr_bind_run; [reflexivity|]
    | |- FPBr (abind (BITS _) _ _) => eapply FPBr_bind_run; [reflexivity|]
    | |- FPBr (abind HOLD _ _) => eapply FPBr_bind_run; [reflexivity|]
    | |- FPBr (abind (us _) _ _) => eapply FPBr_bind_run; [reflexivity|]
    | |- FPBr (abind (uc _) _ _) => eapply FPBr_bind_run; [reflexivity|]
    | |- FPBr (abind (ur _) _ _) => eapply FPBr_bind_run; [reflexivity|]
    | |- FPBr (abind _ _ _) => apply FPBr_bind; [|]
    | |- FPBr ((if ?b then _ else _) _) => destruct b
    | |- FPBr (if ?b then _ else _) => destruct b
    | |- FPBr ((match ?x with _ => _ end) _) => destruct x
    | |- FPBr (match ?x with _ => _ end) => destruct x
    | |- FPBr _ =>
        first [ solve [eauto 3 with fpb nocore]
              | progress (cbv beta zeta delta [aret aleave areturn aget agets gs gc gr us uc ur BITS HOLD DROPBITS INITBITS BYTEBITS
                                              set_mode set_msg go_bad set_adler_check CRC2 CRC4 aux set_back add_back set_lens
                                              PULLBYTE crc_input NEEDBITS DECODE1 DECODE2]) ]
    end.
  Ltac fpb := repeat fpb_step.
  Hint Extern 1 (FPB _) => fpb_state : fpb.

  Lemma NEEDBITS_k_fpb : forall k n w, FPB w -> FPBr (NEEDBITS_k k n w).
  Proof. induction k as [|k IH]; intros n w (F1 & F2 & F3 & F4 & F5 & F6); cbn [NEEDBITS_k]; fpb. Qed.
  Lemma NEEDBITS_fpb : forall n w, FPB w -> FPBr (NEEDBITS n w).
  Proof. intros n w HF. unfold NEEDBITS. apply NEEDBITS_k_fpb. exact HF. Qed.
  Hint Resolve NEEDBITS_fpb : fpb.
  Lemma arm_DONE_fpb : forall w, FPB w -> FPBr (arm_DONE w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5 & F6). unfold arm_DONE. fpb. Qed.
  Hint Resolve arm_DONE_fpb : fpb.
  Lemma arm_LENGTH_fpb : forall w, FPB w -> FPBr (arm_LENGTH w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5 & F6). unfold arm_LENGTH. fpb. Qed.
  Hint Resolve arm_LENGTH_fpb : fpb.
  Lemma arm_BAD_fpb : forall w, FPB w -> FPBr (arm_BAD w).
  Proof. intros w (F1 & F2 & F3 & F4 & F5 & F6). unfold arm_BAD. fpb. Qed.
  Hint Resolve arm_BAD_fpb : fpb.
End FrameB.

Ltac fpb_state :=
  first [ assumption
        | unfold FPB; cbn [w_s w_c w_r wset_s wset_c wset_r RESTORE]; unfold fixedtables; sacc; rewrite ?arr_len_set, ?arr_len_blit;
          repeat match goal with |- _ /\ _ => split end;
          first [ assumption | reflexivity | (intros XX; cbv in XX; discriminate XX)
                | match goal with H : is_mode ?s = _ |- is_mode ?s <> _ => rewrite H; intros XX; cbv in XX; discriminate XX end
                | match goal with |- (if ?b then _ else _) <> _ => destruct b; intros XX; cbv in XX; discriminate XX end
                | (unfold cmodes; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity | right; right; right; reflexivity]) ] ].
Local Hint Extern 1 (FPB _ _ _) => fpb_state : fpb.
Local Hint Resolve NEEDBITS_fpb arm_DONE_fpb arm_LENGTH_fpb arm_BAD_fpb : fpb.
Ltac fpb_step :=
  cbv beta zeta;
  lazymatch goal with
  | |- forall a w, FPB _ _ w -> _ => intros ? ? (?&?&?&?&?&?)
  | |- FPBr _ _ (ARun _ _) => unfold FPBr; fpb_state
  | |- FPBr _ _ (ALeave _) => unfold FPBr; fpb_state
  | |- FPBr _ _ (abind (gs _) _ _) => eapply FPBr_bind_run; [reflexivity|]
  | |- FPBr _ _ (abind (gr _) _ _) => eapply FPBr_bind_run; [reflexivity|]
  | |- FPBr _ _ (abind (gc _) _ _) => eapply FPBr_bind_run; [reflexivity|]
  | |- FPBr _ _ (abind aget _ _) => eapply FPBr_bind_run; [reflexivity|]
  | |- FPBr _ _ (abind (BITS _) _ _) => eapply FPBr_bind_run; [reflexivity|]
  | |- FPBr _ _ (abind HOLD _ _) => eapply FPBr_bind_run; [reflexivity|]
  | |- FPBr _ _ (abind (us _) _ _) => eapply FPBr_bind_run; [reflexivity|]
  | |- FPBr _ _ (abind (uc _) _ _) => eapply FPBr_bind_run; [reflexivity|]
  | |- FPBr _ _ (abind (ur _) _ _) => eapply FPBr_bind_run; [reflexivity|]
  | |- FPBr _ _ (abind _ _ _) => apply FPBr_bind; [|]
  | |- FPBr _ _ ((if ?b then _ else _) _) => destruct b
  | |- FPBr _ _ (if ?b then _ else _) => destruct b
  | |- FPBr _ _ ((match ?x with _ => _ end) _) => destruct x
  | |- FPBr _ _ (match ?x with _ => _ end) => destruct x
  | |- FPBr _ _ _ =>
      first [ solve [eauto 3 with fpb nocore]
            | progress (cbv beta zeta delta [aret aleave areturn aget agets gs gc gr us uc ur BITS HOLD DROPBITS INITBITS BYTEBITS
                                            set_mode set_msg go_bad set_adler_check CRC2 CRC4 aux set_back add_back set_lens
                                            PULLBYTE crc_input NEEDBITS DECODE1 DECODE2]) ]
  end.
Ltac fpb := repeat fpb_step.

Section BK.
  Variable NO : Z.
Variable TOT0 : Z.

  Definition caseA (w : iw) : Prop := ic_total_out (w_c w) = TOT0 /\ ir_out (w_r w) = NO.
  Definition caseB (w : iw) : Prop :=
    ic_total_out (w_c w) = wrap64 (TOT0 + ir_put (w_r w)) /\ ir_out (w_r w) = ir_left (w_r w) /\ cmodes (is_mode (w_s w)).
  Definition BK (w : iw) : Prop :=
    arr_len (ic_outbuf (w_c w)) = NO /\ is_mode (w_s w) <> MEM /\ is_mode (w_s w) <> SYNC /\ (caseA w \/ caseB w).
  Definition BKr {A} (res : ares A) : Prop :=
    match res with ARun _ w => BK w | ALeave w => BK w | ARet rc w => BK w /\ RETOK rc w end.

  Lemma FP_BK : forall w, FP NO TOT0 NO w -> BK w.
  Proof. intros w (F1 & F2 & F3 & F4 & F5). split; [exact F1|]. split; [exact F4|]. split; [exact F5|]. left. exact (conj F2 F3). Qed.
  Lemma FPr_BKr : forall {A} (res : ares A), FPr NO TOT0 NO res -> BKr res.
  Proof. intros A [a w|w|rc w]; cbn [FPr BKr]; [apply FP_BK | apply FP_BK | intros [H1 H2]; split; [apply FP_BK; exact H1 | exact H2]]. Qed.

  Lemma FPB_BK : forall w, FPB NO TOT0 w -> BK w.
  Proof. intros w (F1 & F2 & F3 & F4 & F5 & F6). split; [exact F1|]. split; [exact F4|]. split; [exact F5|]. right. exact (conj F2 (conj F3 F6)). Qed.
  Lemma FPBr_BKr : forall {A} (res : ares A), FPBr NO TOT0 res -> BKr res.
  Proof. intros A [a w|w|rc w]; cbn [FPBr BKr]; [apply FPB_BK | apply FPB_BK | intros [H1 H2]; split; [apply FPB_BK; exact H1 | exact H2]]. Qed.
  Lemma BK_FPA : forall w, BK w -> caseA w -> FP NO TOT0 NO w.
  Proof. intros w (B1 & B2 & B3 & _) [A1 A2]. exact (conj B1 (conj A1 (conj A2 (conj B2 B3)))). Qed.
  Lemma BK_FPB : forall w, BK w -> caseB w -> FPB NO TOT0 w.
  Proof. intros w (B1 & B2 & B3 & _) (C1 & C2 & C3). exact (conj B1 (conj C1 (conj C2 (conj B2 (conj B3 C3))))). Qed.

  Ltac brun := aflat; unfold abind at 1; first [rewrite aret_eq | rewrite gs_eq | rewrite gr_eq | rewrite us_eq | rewrite uc_eq | rewrite ur_eq | idtac];
               cbv beta iota.

  Section Dispatch.
    Variable flush : Z.

    Lemma arm_CHECK_bk : forall s c r, WINV (mkW s c r) -> is_mode s = CHECK -> BK (mkW s c r) -> BKr (arm_CHECK (mkW s c r)).
    Proof.
      intros s c r HW E HB. pose proof HB as (B1 & B2 & B3 & HAB). cbn [w_s w_c w_r] in *.
      unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (HC & HR & _). regs_open HR.
      unfold arm_CHECK. brun.
      destruct (negb (is_wrap s =? 0)) eqn:EW.
      2:{
          brun. destruct HAB as [[A1 A2]|HCB].
          - apply FPr_BKr. unfold set_mode. aflat. eapply FPr_bind_run; [reflexivity|]. apply arm_LENGTH_fp.
            unfold FP. cbn [w_s w_c w_r wset_s]. sacc. repeat split; first [exact B1 | exact A1 | exact A2 | discriminate].
          - apply FPBr_BKr. unfold set_mode. aflat. eapply FPBr_bind_run; [reflexivity|]. apply arm_LENGTH_fpb.
            destruct HCB as (C1 & C2 & C3). unfold FPB. cbn [w_s w_c w_r wset_s]. sacc. repeat split; first [exact B1 | exact C1 | exact C2 | discriminate | right; left; reflexivity]. }
      aflat. unfold abind at 1.
      destruct (NEEDBITS_spec c 32 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & _)|(r1 & EQ & HR1 & HP1 & _)]; rewrite EQ;
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _).
      2:{ cbn [BKr]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
          destruct HAB as [[A1 A2]|(C1 & C2 & C3)]; [left | right]; unfold caseA, caseB; cbn [w_s w_c w_r]; rewrite ?Eo1, ?Ep1, ?El1.
          - exact (conj A1 A2).
          - exact (conj C1 (conj C2 C3)). }
      cbv beta iota. pose proof HR1 as (_ & _ & _ & RP1 & RL1 & RPL1 & _).
      assert (Etot : wrap64 (ic_total_out c + wrap32 (ir_out r1 - ir_left r1)) = wrap64 (TOT0 + ir_put r1)).
      { destruct HAB as [[A1 A2]|(C1 & C2 & C3)]; cbn [w_s w_c w_r] in *.
        - rewrite Eo1, El1, A2, A1, <- B1, <- RPL, Ep1. replace (ir_put r + ir_left r - ir_left r) with (ir_put r) by lia. rewrite wrap32_id by lia. reflexivity.
        - rewrite Eo1, El1, C2, C1, Ep1. replace (ir_left r - ir_left r) with 0 by lia. change (wrap32 0) with 0. rewrite Z.add_0_r.
          rewrite wrap64_mod, wrap64_mod, Z.mod_mod by lia. reflexivity. }
      brun. brun. brun. brun. brun. sacc.
      set (OUT := wrap32 (ir_out r1 - ir_left r1)) in *.

      destruct (negb (Z.land (is_wrap s) 4 =? 0) && negb (OUT =? 0)).
      1: brun; unfold set_adler_check; brun; brun.
      2: brun.
      all: brun; sacc.
      all: match goal with |- BKr (?p ?w9) =>
             assert (HB9 : FPB NO TOT0 w9)
               by (unfold FPB; cbn [w_s w_c w_r]; sacc; rewrite Etot; repeat split; first [exact B1 | reflexivity | rewrite E; discriminate | left; exact E]);
             apply FPBr_BKr; destruct HB9 as (?&?&?&?&?&?); fpb end.
    Qed.

    Theorem dispatch_bk : forall s c r, WINV (mkW s c r) -> BK (mkW s c r) -> BKr (dispatch ivar_ref flush (mkW s c r)).
    Proof.
      intros s c r HW HB. pose proof HB as (B1 & B2 & B3 & HAB). cbn [w_s w_c w_r] in B1, B2, B3.
      unfold dispatch. unfold abind. rewrite gs_eq. cbv zeta.

      Ltac tryA HAB lem := lazymatch goal with |- BKr ((if is_mode ?s =? ?M then _ else _) _) =>
        destruct (Z.eqb_spec (is_mode s) M) as [E|?NE];
        [ destruct HAB as [HA|(_ & _ & HM)];
          [ apply FPr_BKr; apply lem; try exact E; apply BK_FPA; assumption
          | exfalso; unfold cmodes in HM; cbn [w_s w_c w_r] in HM; rewrite E in HM; destruct HM as [X|[X|[X|X]]]; discriminate X ]
        | ] end.

      Ltac tryAB HAB lemA lemB := lazymatch goal with |- BKr ((if is_mode ?s =? ?M then _ else _) _) =>
        destruct (Z.eqb_spec (is_mode s) M) as [E|?NE];
        [ destruct HAB as [HA|HCB];
          [ apply FPr_BKr; apply lemA; apply BK_FPA; assumption
          | apply FPBr_BKr; apply lemB; apply BK_FPB; assumption ]
        | ] end.
      tryA HAB (arm_HEAD_fp NO TOT0 NO ivar_ref). tryA HAB (arm_FLAGS_fp NO TOT0 NO). tryA HAB (arm_TIME_fp NO TOT0 NO). tryA HAB (arm_OS_fp NO TOT0 NO).
      tryA HAB (arm_EXLEN_fp NO TOT0 NO). tryA HAB (arm_EXTRA_fp NO TOT0 NO). tryA HAB (arm_NAME_fp NO TOT0 NO). tryA HAB (arm_COMMENT_fp NO TOT0 NO).
      tryA HAB (arm_HCRC_fp NO TOT0 NO). tryA HAB (arm_DICTID_fp NO TOT0 NO ivar_ref flush). tryA HAB (arm_DICT_fp NO TOT0 NO ivar_ref flush).
      tryA HAB (arm_TYPE_fp NO TOT0 NO ivar_ref flush). tryA HAB (arm_TYPEDO_fp NO TOT0 NO ivar_ref flush). tryA HAB (arm_STORED_fp NO TOT0 NO ivar_ref flush).
      tryA HAB (arm_COPY__fp NO TOT0 NO). tryA HAB (arm_COPY_fp NO TOT0 NO). tryA HAB (arm_TABLE_fp NO TOT0 NO ivar_ref flush).
      tryA HAB (arm_LENLENS_fp NO TOT0 NO ivar_ref flush). tryA HAB (arm_CODELENS_fp NO TOT0 NO ivar_ref flush).
      tryA HAB (arm_LEN__fp NO TOT0 NO ivar_ref). tryA HAB (arm_LEN_fp NO TOT0 NO ivar_ref). tryA HAB (arm_LENEXT_fp NO TOT0 NO ivar_ref).
      tryA HAB (arm_DIST_fp NO TOT0 NO ivar_ref). tryA HAB (arm_DISTEXT_fp NO TOT0 NO ivar_ref). tryA HAB (arm_MATCH_fp NO TOT0 NO ivar_ref).
      tryA HAB (arm_LIT_fp NO TOT0 NO).

      destruct (Z.eqb_spec (is_mode s) CHECK) as [E|NEck]; [exact (arm_CHECK_bk s c r HW E HB)|].
      tryAB HAB (arm_LENGTH_fp NO TOT0 NO) (arm_LENGTH_fpb NO TOT0).
      tryAB HAB (arm_DONE_fp NO TOT0 NO) (arm_DONE_fpb NO TOT0).
      tryAB HAB (arm_BAD_fp NO TOT0 NO) (arm_BAD_fpb NO TOT0).

      destruct (Z.eqb_spec (is_mode s) MEM) as [E|NE']; [exfalso; exact (B2 E)|].
      exfalso. unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (_ & _ & HMF & _). unfold MF in HMF.
      repeat match goal with N : is_mode s <> ?K |- _ => rewrite (proj2 (Z.eqb_neq _ _) N) in HMF; clear N end.
      destruct (Z.eqb_spec (is_mode s) SYNC) as [E|NE'']; [exact (B3 E)|].
      rewrite ?(proj2 (Z.eqb_neq _ _) NE'') in HMF. cbn [orb] in HMF. exact HMF.
    Qed.
  End Dispatch.
End BK.

Definition IPOST (zc : ZCall) (p : inflate_state * ZRet) : Prop :=
  let zr := snd p in
  0 <= zlength (zr_output zr) <= zc_avail_out zc
  /\ (zr_rc zr = Z_OK \/ zr_rc zr = Z_STREAM_END ->
      zs_total_out (zr_strm zr) = wrap64 (zs_total_out (zc_strm zc) + zlength (zr_output zr))).

Section Call.
  Variable flush : Z.

  Lemma inf_loop_bk_nat : forall NO TOT0 m w, WINV w -> BK NO TOT0 w -> PHI w < Z.of_nat m ->
    let '(stop, w') := iterZ (Z.of_nat m) (lstep flush) (fun w0 => (SLeave, w0)) w in
    WINV w' /\ BK NO TOT0 w' /\ match stop with SLeave => True | SRet rc => RETOK rc w' end.
  Proof.
    intros NO TOT0. induction m as [|m IH]; intros w HW HB HP.
    { exfalso. pose proof (PHI_nonneg w HW). cbn in HP. lia. }
    rewrite iterZ_step by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
    unfold lstep at 1. destruct w as [s c r].
    pose proof (dispatch_safe flush (mkW s c r) s c r HW ltac:(lia)) as D.
    pose proof (dispatch_bk NO TOT0 flush s c r HW HB) as B.
    destruct (dispatch ivar_ref flush (mkW s c r)) as [u w'|w'|rc w']; cbn [BKr] in B.
    - destruct D as [HW' HP']. apply IH; [exact HW'|exact B|lia].
    - split; [exact D|]. split; [exact B|exact I].
    - split; [exact (proj1 D)|]. exact B.
  Qed.

  Lemma inf_loop_bk : forall NO TOT0 w, WINV w -> BK NO TOT0 w ->
    PHI w < 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64) ->
    let '(stop, w') := inf_loop ivar_ref flush w in
    WINV w' /\ BK NO TOT0 w' /\ match stop with SLeave => True | SRet rc => RETOK rc w' end.
  Proof.
    intros NO TOT0 w HW HB HP. unfold inf_loop. change (fun w0 : iw => _) with (lstep flush) at 1.
    pose proof (PHI_nonneg w HW).
    rewrite <- (Z2Nat.id (64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64))) by lia.
    apply inf_loop_bk_nat; [exact HW|exact HB|]. rewrite Z2Nat.id by lia. exact HP.
  Qed.

  Theorem inflate_m_post : forall s zc ch p,
    INV s -> ZC zc -> ipure (inflate_m ivar_ref hooks_pure s zc flush) ch = Some p -> IPOST zc p.
  Proof.
    intros s zc ch p HI Hz E. pose proof Hz as (Hao & Hlen & Hby). pose proof (zlength_nonneg (zc_input zc)) as LN.
    unfold ipure in E. rewrite (inflate_m_W0 hooks_pure) in E by (apply INV_check; exact HI).
    destruct (Z.eq_dec (is_mode s) MEM) as [EM|NM].
    - rewrite (inf_loop_MEM flush (W0 s zc)) in E; cycle 1.
      { unfold W0, s_entry. cbn [w_s]. rewrite EM. change (MEM =? TYPE) with false. cbv iota. exact EM. }
      { cbn [W0 w_c icall_of_zcall ic_avail_in]. lia. }
      { cbn [W0 w_c icall_of_zcall ic_avail_out]. lia. }
      unfold sret in E. cbn [fst] in E. injection E; intros <-. unfold IPOST. cbn [snd W0 w_c zret_of_icall zr_output zr_rc icall_of_zcall ic_outbuf ic_next_out].
      rewrite arr_slice_length. split; [lia|]. intros [X|X]; discriminate X.
    - destruct (WINV_entry' s zc HI Hz) as [HW HP].
      assert (HB : BK (zc_avail_out zc) (zs_total_out (zc_strm zc)) (W0 s zc)).
      { unfold BK, caseA. cbn [W0 w_s w_c w_r icall_of_zcall ic_outbuf ic_total_out ir_out]. unfold arr_make. rewrite arr_len_init.
        split; [reflexivity|]. unfold s_entry.
        assert (NS : is_mode s <> SYNC) by (intros ES; destruct HI as (_ & _ & HM); rewrite ES in HM; exact HM).
        destruct (Z.eqb_spec (is_mode s) TYPE) as [ET|ET]; sacc; [split; [discriminate|]; split; [discriminate|] | split; [exact NM|]; split; [exact NS|]]; left; split; reflexivity. }
      pose proof (inf_loop_bk (zc_avail_out zc) (zs_total_out (zc_strm zc)) (W0 s zc) HW HB HP) as L.
      destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop [s' c' r']]. destruct L as (HW' & HB' & HR').
      pose proof HW' as HW0. unfold WINV in HW'. cbn [w_s w_c w_r] in HW'. destruct HW' as (_ & HREG & _).
      pose proof HREG as (RN & RH & RNH & RP & RL & RPL & _ & _ & _ & RNO).
      destruct HB' as (B1 & B2 & B3 & HAB). unfold caseA, caseB in HAB. cbn [w_s w_c w_r] in B1, B2, B3, HAB.
      destruct stop as [|rc].
      +
        rewrite (inf_leave_eq hooks_pure) in E. unfold sbind in E.
        assert (TAIL : forall s2 ch',
                  match @sret CH _ (lv_fin flush s2 (c_rest c' r') r') ch' with MRet q => Some (fst q) | _ => None end = Some p -> IPOST zc p).
        { intros s2 ch' X. unfold sret in X. cbn [fst] in X. injection X; intros <-. unfold IPOST, lv_fin. cbv zeta.
          match goal with |- context [if ?cnd then _ else _] => destruct cnd end; cbn [fst snd zret_of_icall zr_output zr_rc zr_strm zstrm_of_icall zs_total_out];
            unfold c_rest; sacc; rewrite arr_slice_length.
          all: split; [clear - B1 RPL RP RL; lia|]; intros _.
          all: destruct HAB as [[A1 A2]|(C1 & C2 & C3)]; rewrite ?A1, ?A2, ?C1, ?C2.
          1,3: replace (zc_avail_out zc - ir_left r') with (ir_put r') by (clear - B1 RPL; lia); rewrite wrap32_id by (clear - B1 RPL RP RL RNO; lia);
               rewrite Z.max_r by exact RP; reflexivity.
          all: replace (ir_left r' - ir_left r') with 0 by lia; change (wrap32 0) with 0; rewrite Z.add_0_r; rewrite Z.max_r by exact RP;
               rewrite !wrap64_mod, Z.mod_mod by lia; reflexivity. }
        destruct (lv_cond flush (s_rest s' r') (c_rest c' r') r').
        * rewrite updatewindow_pure in E. cbn [mbind fst snd] in E.
          destruct (uw_pure (s_rest s' r') _ _ _ ch) as [s2|].
          -- exact (TAIL s2 ch E).
          -- unfold sret in E. injection E; intros <-. unfold IPOST, lv_mem. cbn [fst snd zret_of_icall zr_output zr_rc].
             destruct (lv_pre_fields (s_rest s' r') (c_rest c' r') r') as (_ & _ & _ & _ & F5 & F6). rewrite F5, F6. unfold c_rest. sacc.
             rewrite arr_slice_length. split; [clear - B1 RPL RP RL; lia|]. intros [X|X]; discriminate X.
        * unfold sret at 1 in E. cbn [mbind fst snd] in E. exact (TAIL (s_rest s' r') ch E).
      +
        unfold sret in E. cbn [fst] in E. injection E; intros <-. destruct HR' as [-> Hno].
        cbn [w_c w_r] in Hno. unfold IPOST. cbn [fst snd zret_of_icall zr_output zr_rc]. rewrite Hno, arr_slice_length.
        split; [clear - B1 RPL RP RL; lia|]. intros [X|X]; discriminate X.
  Qed.
End Call.
