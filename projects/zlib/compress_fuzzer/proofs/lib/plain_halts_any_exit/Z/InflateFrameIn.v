(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflate_runA.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeS1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeS2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeS3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeFR.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeTY.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateEqD.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateEqF.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateEqS.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FrameI.
  Variable TI0 : Z.
  Variable I0 : Z.
  Variable NI : Z.

  Definition FI (w : iw) : Prop :=
    ic_total_in (w_c w) = TI0 /\ ir_in (w_r w) = I0 /\ arr_len (ic_input (w_c w)) = NI
    /\ - 2 ^ 31 <= ir_ret (w_r w) < 2 ^ 31.
  (* zlib 1.4: a direct return may move total_in (DICT adds in - avail_in before Z_NEED_DICT, inflate.c), so the
     return frame drops the total_in cell; the leave frame keeps it *)
  Definition FIR (w : iw) : Prop :=
    ir_in (w_r w) = I0 /\ arr_len (ic_input (w_c w)) = NI /\ - 2 ^ 31 <= ir_ret (w_r w) < 2 ^ 31.
  Lemma FI_FIR : forall w, FI w -> FIR w.
  Proof. intros w (F1 & F2 & F3 & F4). split; [exact F2|]. split; [exact F3|exact F4]. Qed.
  Definition FIr {A} (res : ares A) : Prop :=
    match res with ARun _ w => FI w | ALeave w => FI w | ARet rc w => FIR w /\ - 2 ^ 31 <= rc < 2 ^ 31 end.

  Section Rules.
    Context {A B : Type}.
    Lemma FPr_bind : forall (m : AM A) (f : A -> AM B) w,
      FIr (m w) -> (forall a w', FI w' -> FIr (f a w')) -> FIr (abind m f w).
    Proof. intros m f w Hm Hf. unfold abind. destruct (m w) as [a w'|w'|rc w']; [exact (Hf a w' Hm) | exact Hm | exact Hm]. Qed.
    Lemma FPr_bind_run : forall (m : AM A) (f : A -> AM B) w a w',
      m w = ARun a w' -> FIr (f a w') -> FIr (abind m f w).
    Proof. intros m f w a w' E H. unfold abind. rewrite E. exact H. Qed.
  End Rules.

  Lemma restore_fi : forall w, FI w -> FIr (amodify RESTORE w).
  Proof. intros [s c r] (F1 & F2 & F3 & F4). unfold FIr, amodify, RESTORE, FI. cbn [w_s w_c w_r] in *. sacc. repeat split; first [assumption | lia]. Qed.

  Lemma fast_fi : forall w, is_mode (w_s w) = LEN -> FI w -> FIr (amodify (fun w0 => LOAD (inflate_fast (RESTORE w0))) w).
  Proof.
    intros [s c r] E (F1 & F2 & F3 & F4). cbn [w_s w_c w_r] in *. unfold FIr, amodify, RESTORE. cbn [w_s w_c w_r].
    match goal with |- context [inflate_fast (mkW ?a ?b ?d)] =>
      rewrite (inflate_fast_eqo a b d); destruct (ff_loopo a b d) as [f mm] end.
    unfold ff_posto, LOAD. cbv zeta.
    destruct mm as [[md [mg|]]|]; cbn [w_s w_c w_r]; unfold wset_r, FI; cbn [w_s w_c w_r]; sacc; repeat split; first [assumption | lia].
  Qed.

  Ltac fi_state :=
    first [ assumption
          | unfold FI; cbn [w_s w_c w_r wset_s wset_c wset_r RESTORE]; unfold fixedtables; sacc; rewrite ?arr_len_set, ?arr_len_blit;
            repeat match goal with |- _ /\ _ => split end;
            first [ assumption | reflexivity | (intros XX; cbv in XX; discriminate XX)
                  | (unfold Z_OK, Z_STREAM_END, Z_DATA_ERROR, Z_MEM_ERROR, Z_NEED_DICT, Z_BUF_ERROR, Z_STREAM_ERROR; lia)
                  | lia
                  | match goal with IT : inflate_table _ _ _ _ _ _ _ _ = (?ret, _, _, _, _) |- _ =>
                      destruct (inflate_table_ret _ _ _ _ _ _ _ _ _ _ _ _ _ IT) as [E0 | [E0 | E0]]; rewrite E0; lia end
                  | match goal with H : is_mode ?s = _ |- is_mode ?s <> _ => rewrite H; intros XX; cbv in XX; discriminate XX end
                  | match goal with |- (if ?b then _ else _) <> _ => destruct b; intros XX; cbv in XX; discriminate XX end ] ].

  Create HintDb fi discriminated.

  Ltac fi_step :=
    cbv beta zeta;
    lazymatch goal with
    | |- forall a w, FI w -> _ => intros ? ? (?&?&?&?)
    | |- FIr (ARun _ _) => unfold FIr; fi_state
    | |- FIr (ALeave _) => unfold FIr; fi_state
    | |- FIr (ARet _ _) => unfold FIr; split; [unfold FIR; fi_state | unfold Z_OK, Z_STREAM_END, Z_DATA_ERROR, Z_MEM_ERROR, Z_NEED_DICT, Z_BUF_ERROR, Z_STREAM_ERROR; lia]
    | |- FIr (abind (gs _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FIr (abind (gr _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FIr (abind (gc _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FIr (abind aget _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FIr (abind (BITS _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FIr (abind HOLD _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FIr (abind (us _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FIr (abind (uc _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FIr (abind (ur _) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FIr (abind (amodify RESTORE) _ _) => eapply FPr_bind_run; [reflexivity|]
    | |- FIr (abind _ _ _) => apply FPr_bind; [|]
    | |- FIr ((if ?b then _ else _) _) => destruct b
    | |- FIr (if ?b then _ else _) => destruct b
    | |- FIr (match match_copy ?wn ?st with _ => _ end) => destruct (match_copy wn st) as [[[? ?] ?] ?]
    | |- FIr ((match inflate_table ?a ?b ?c ?d ?e ?f ?g ?h with _ => _ end) _) => destruct (inflate_table a b c d e f g h) eqn:?IT
    | |- FIr (match inflate_table ?a ?b ?c ?d ?e ?f ?g ?h with _ => _ end) => destruct (inflate_table a b c d e f g h) eqn:?IT
    | |- FIr ((match ?x with _ => _ end) _) => destruct x
    | |- FIr (match ?x with _ => _ end) => destruct x
    | |- FIr (amodify RESTORE _) => apply restore_fi; fi_state
    | |- FIr (amodify _ _) => apply fast_fi; [cbn [w_s wset_s wset_c wset_r]; sacc; first [assumption | reflexivity] | fi_state]
    | |- FIr _ =>
        first [ solve [eauto 3 with fi nocore]
              | progress (cbv beta zeta delta [aret aleave areturn aget agets gs gc gr us uc ur BITS HOLD DROPBITS INITBITS BYTEBITS
                                              set_mode set_msg go_bad set_adler_check CRC2 CRC4 aux set_back add_back set_lens
                                              PULLBYTE crc_input NEEDBITS DECODE1 DECODE2]) ]
    end.
  Ltac fi := repeat fi_step.

  Hint Extern 1 (FI _) => fi_state : fi.

  Lemma NEEDBITS_k_fi : forall k n w, FI w -> FIr (NEEDBITS_k k n w).
  Proof. induction k as [|k IH]; intros n w (F1 & F2 & F3 & F4); cbn [NEEDBITS_k]; fi. Qed.
  Lemma NEEDBITS_fi : forall n w, FI w -> FIr (NEEDBITS n w).
  Proof. intros n w HF. unfold NEEDBITS. apply NEEDBITS_k_fi. exact HF. Qed.
  Hint Resolve NEEDBITS_fi : fi.

  Lemma DECODE_k_fi : forall k p index need w, FI w -> FIr (DECODE_k k p index need w).
  Proof. induction k as [|k IH]; intros p index need w (F1 & F2 & F3 & F4); cbn [DECODE_k]; fi. Qed.
  Lemma DECODE1_fi : forall p n w, FI w -> FIr (DECODE1 p n w).
  Proof. intros p n w HF. unfold DECODE1. apply DECODE_k_fi. exact HF. Qed.
  Lemma DECODE2_fi : forall p l w, FI w -> FIr (DECODE2 p l w).
  Proof. intros p l w HF. unfold DECODE2. apply DECODE_k_fi. exact HF. Qed.
  Hint Resolve DECODE1_fi DECODE2_fi : fi.

  Lemma lens_repeat_fi : forall copy len w, FI w -> FIr (lens_repeat copy len w).
  Proof.
    intros copy len [s c r] (F1 & F2 & F3 & F4). unfold lens_repeat, us, FIr. cbn [w_s w_c w_r wset_s].
    lazymatch goal with |- context [loopZ ?n ?st ?a] => destruct (loopZ n st a) as [[l h] cp] end.
    unfold FI. cbn [w_s w_c w_r] in *. sacc. repeat split; first [assumption | lia].
  Qed.
  Hint Resolve lens_repeat_fi : fi.

  Lemma arm_DONE_fi : forall w, FI w -> FIr (arm_DONE w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_DONE. fi. Qed.
  Hint Resolve arm_DONE_fi : fi.
  Lemma arm_LENGTH_fi : forall w, FI w -> FIr (arm_LENGTH w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_LENGTH. fi. Qed.
  Hint Resolve arm_LENGTH_fi : fi.
  Lemma arm_BAD_fi : forall w, FI w -> FIr (arm_BAD w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_BAD. fi. Qed.
  Hint Resolve arm_BAD_fi : fi.
  Lemma arm_LIT_fi : forall w, FI w -> FIr (arm_LIT w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_LIT. fi. Qed.
  Hint Resolve arm_LIT_fi : fi.
  Lemma arm_MATCH_fi : forall iv w, FI w -> FIr (arm_MATCH iv w).
  Proof. intros iv w (F1 & F2 & F3 & F4). unfold arm_MATCH. fi. Qed.
  Hint Resolve arm_MATCH_fi : fi.
  Lemma arm_DISTEXT_fi : forall iv w, FI w -> FIr (arm_DISTEXT iv w).
  Proof. intros iv w (F1 & F2 & F3 & F4). unfold arm_DISTEXT. fi. Qed.
  Hint Resolve arm_DISTEXT_fi : fi.
  Lemma arm_DIST_fi : forall iv w, FI w -> FIr (arm_DIST iv w).
  Proof. intros iv w (F1 & F2 & F3 & F4). unfold arm_DIST. fi. Qed.
  Hint Resolve arm_DIST_fi : fi.
  Lemma arm_LENEXT_fi : forall iv w, FI w -> FIr (arm_LENEXT iv w).
  Proof. intros iv w (F1 & F2 & F3 & F4). unfold arm_LENEXT. fi. Qed.
  Hint Resolve arm_LENEXT_fi : fi.
  Lemma arm_LEN_fi : forall iv w, is_mode (w_s w) = LEN -> FI w -> FIr (arm_LEN iv w).
  Proof. intros iv w E (F1 & F2 & F3 & F4). unfold arm_LEN. fi. Qed.
  Hint Resolve arm_LEN_fi : fi.
  Lemma arm_LEN__fi : forall iv w, FI w -> FIr (arm_LEN_ iv w).
  Proof. intros iv w (F1 & F2 & F3 & F4). unfold arm_LEN_, set_mode. eapply FPr_bind_run; [reflexivity|]. apply arm_LEN_fi; [reflexivity|fi_state]. Qed.
  Hint Resolve arm_LEN__fi : fi.
  Lemma codelens_body_fi : forall w, FI w -> FIr (codelens_body w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold codelens_body. fi. Qed.
  Hint Resolve codelens_body_fi : fi.
  Lemma codelens_while_fi : forall k w, FI w -> FIr (codelens_while k w).
  Proof. induction k as [|k IH]; intros w (F1 & F2 & F3 & F4); cbn [codelens_while]; fi. Qed.
  Hint Resolve codelens_while_fi : fi.
  Lemma arm_CODELENS_fi : forall iv flush w, FI w -> FIr (arm_CODELENS iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4). unfold arm_CODELENS. fi. Qed.
  Hint Resolve arm_CODELENS_fi : fi.
  Lemma lenlens_while1_fi : forall k w, FI w -> FIr (lenlens_while1 k w).
  Proof. induction k as [|k IH]; intros w (F1 & F2 & F3 & F4); cbn [lenlens_while1]; fi. Qed.
  Hint Resolve lenlens_while1_fi : fi.
  Lemma lenlens_while2_fi : forall k w, FI w -> FIr (lenlens_while2 k w).
  Proof. induction k as [|k IH]; intros w (F1 & F2 & F3 & F4); cbn [lenlens_while2]; fi. Qed.
  Hint Resolve lenlens_while2_fi : fi.
  Lemma arm_LENLENS_fi : forall iv flush w, FI w -> FIr (arm_LENLENS iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4). unfold arm_LENLENS. fi. Qed.
  Hint Resolve arm_LENLENS_fi : fi.
  Lemma arm_TABLE_fi : forall iv flush w, FI w -> FIr (arm_TABLE iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4). unfold arm_TABLE. fi. Qed.
  Hint Resolve arm_TABLE_fi : fi.
  Lemma arm_COPY_fi : forall w, FI w -> FIr (arm_COPY w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_COPY. fi. Qed.
  Hint Resolve arm_COPY_fi : fi.
  Lemma arm_COPY__fi : forall w, FI w -> FIr (arm_COPY_ w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_COPY_. fi. Qed.
  Hint Resolve arm_COPY__fi : fi.
  Lemma arm_STORED_fi : forall iv flush w, FI w -> FIr (arm_STORED iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4). unfold arm_STORED. fi. Qed.
  Hint Resolve arm_STORED_fi : fi.
  Lemma arm_TYPEDO_fi : forall iv flush w, FI w -> FIr (arm_TYPEDO iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4). unfold arm_TYPEDO. fi. Qed.
  Hint Resolve arm_TYPEDO_fi : fi.
  Lemma arm_TYPE_fi : forall iv flush w, FI w -> FIr (arm_TYPE iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4). unfold arm_TYPE. fi. Qed.
  Hint Resolve arm_TYPE_fi : fi.
  Lemma arm_DICT_fi : forall iv flush w, FI w -> FIr (arm_DICT iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4). unfold arm_DICT. fi. Qed.
  Hint Resolve arm_DICT_fi : fi.
  Lemma arm_DICTID_fi : forall iv flush w, FI w -> FIr (arm_DICTID iv flush w).
  Proof. intros iv flush w (F1 & F2 & F3 & F4). unfold arm_DICTID. fi. Qed.
  Hint Resolve arm_DICTID_fi : fi.
  Lemma arm_HCRC_fi : forall w, FI w -> FIr (arm_HCRC w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_HCRC. fi. Qed.
  Hint Resolve arm_HCRC_fi : fi.
  Lemma name_like_fi : forall fl w, FI w -> FIr (name_like fl w).
  Proof. intros fl w (F1 & F2 & F3 & F4). unfold name_like. fi. Qed.
  Hint Resolve name_like_fi : fi.
  Lemma arm_COMMENT_fi : forall w, FI w -> FIr (arm_COMMENT w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_COMMENT. fi. Qed.
  Hint Resolve arm_COMMENT_fi : fi.
  Lemma arm_NAME_fi : forall w, FI w -> FIr (arm_NAME w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_NAME. fi. Qed.
  Hint Resolve arm_NAME_fi : fi.
  Lemma arm_EXTRA_fi : forall w, FI w -> FIr (arm_EXTRA w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_EXTRA. fi. Qed.
  Hint Resolve arm_EXTRA_fi : fi.
  Lemma arm_EXLEN_fi : forall w, FI w -> FIr (arm_EXLEN w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_EXLEN. fi. Qed.
  Hint Resolve arm_EXLEN_fi : fi.
  Lemma arm_OS_fi : forall w, FI w -> FIr (arm_OS w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_OS. fi. Qed.
  Hint Resolve arm_OS_fi : fi.
  Lemma arm_TIME_fi : forall w, FI w -> FIr (arm_TIME w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_TIME. fi. Qed.
  Hint Resolve arm_TIME_fi : fi.
  Lemma arm_FLAGS_fi : forall w, FI w -> FIr (arm_FLAGS w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_FLAGS. fi. Qed.
  Hint Resolve arm_FLAGS_fi : fi.
  Lemma arm_HEAD_fi : forall iv w, FI w -> FIr (arm_HEAD iv w).
  Proof. intros iv w (F1 & F2 & F3 & F4). unfold arm_HEAD. fi. Qed.
  Hint Resolve arm_HEAD_fi : fi.
  Lemma arm_CHECK_fi : forall w, FI w -> FIr (arm_CHECK w).
  Proof. intros w (F1 & F2 & F3 & F4). unfold arm_CHECK. fi. Qed.
  Hint Resolve arm_CHECK_fi : fi.
End FrameI.

Section LoopI.
  Variable TI0 : Z.
  Variable I0 : Z.
  Variable NI : Z.
  Variable flush : Z.
  Local Abbreviation FI := (FI TI0 I0 NI).
  Local Abbreviation FIr := (@FIr TI0 I0 NI).
  Local Abbreviation FIR := (FIR I0 NI).

  Lemma arm_MEM_fi : forall w, FI w -> FIr (arm_MEM w).
  Proof. intros w H. split; [exact (FI_FIR TI0 I0 NI w H) | unfold Z_MEM_ERROR; lia]. Qed.
  Lemma arm_SYNC_fi : forall w, FI w -> FIr (arm_SYNC w).
  Proof. intros w H. split; [exact (FI_FIR TI0 I0 NI w H) | unfold Z_STREAM_ERROR; lia]. Qed.

  Theorem dispatch_fi : forall w, FI w -> FIr (dispatch ivar_ref flush w).
  Proof.
    intros [s c r] HF. unfold dispatch. unfold abind. rewrite gs_eq. cbv zeta.
    Ltac tryI HF lem := lazymatch goal with |- InflateFrameIn.FIr _ _ _ ((if is_mode ?s =? ?M then _ else _) _) =>
      destruct (Z.eqb_spec (is_mode s) M) as [E|?NE]; [apply lem; first [exact E | exact HF] |] end.
    tryI HF (arm_HEAD_fi TI0 I0 NI ivar_ref). tryI HF (arm_FLAGS_fi TI0 I0 NI). tryI HF (arm_TIME_fi TI0 I0 NI). tryI HF (arm_OS_fi TI0 I0 NI).
    tryI HF (arm_EXLEN_fi TI0 I0 NI). tryI HF (arm_EXTRA_fi TI0 I0 NI). tryI HF (arm_NAME_fi TI0 I0 NI). tryI HF (arm_COMMENT_fi TI0 I0 NI).
    tryI HF (arm_HCRC_fi TI0 I0 NI). tryI HF (arm_DICTID_fi TI0 I0 NI ivar_ref flush). tryI HF (arm_DICT_fi TI0 I0 NI ivar_ref flush).
    tryI HF (arm_TYPE_fi TI0 I0 NI ivar_ref flush). tryI HF (arm_TYPEDO_fi TI0 I0 NI ivar_ref flush). tryI HF (arm_STORED_fi TI0 I0 NI ivar_ref flush).
    tryI HF (arm_COPY__fi TI0 I0 NI). tryI HF (arm_COPY_fi TI0 I0 NI). tryI HF (arm_TABLE_fi TI0 I0 NI ivar_ref flush).
    tryI HF (arm_LENLENS_fi TI0 I0 NI ivar_ref flush). tryI HF (arm_CODELENS_fi TI0 I0 NI ivar_ref flush).
    tryI HF (arm_LEN__fi TI0 I0 NI ivar_ref). tryI HF (arm_LEN_fi TI0 I0 NI ivar_ref). tryI HF (arm_LENEXT_fi TI0 I0 NI ivar_ref).
    tryI HF (arm_DIST_fi TI0 I0 NI ivar_ref). tryI HF (arm_DISTEXT_fi TI0 I0 NI ivar_ref). tryI HF (arm_MATCH_fi TI0 I0 NI ivar_ref).
    tryI HF (arm_LIT_fi TI0 I0 NI). tryI HF (arm_CHECK_fi TI0 I0 NI). tryI HF (arm_LENGTH_fi TI0 I0 NI). tryI HF (arm_DONE_fi TI0 I0 NI).
    tryI HF (arm_BAD_fi TI0 I0 NI). tryI HF arm_MEM_fi.
    exact (arm_SYNC_fi _ HF).
  Qed.

  (* zlib 1.4: the full frame (total_in included) holds at a leave; a direct return keeps FIR and the rc range *)
  Theorem inf_loop_fi : forall w, FI w ->
    match fst (inf_loop ivar_ref flush w) with
    | SRet rc => FIR (snd (inf_loop ivar_ref flush w)) /\ - 2 ^ 31 <= rc < 2 ^ 31
    | SLeave => FI (snd (inf_loop ivar_ref flush w))
    end.
  Proof.
    intros w HF. unfold inf_loop.
    apply (RefInflateSafeFR.iterZ_ind2 (fun a => FI a)
             (fun b : istop * iw => match fst b with SRet rc => FIR (snd b) /\ - 2 ^ 31 <= rc < 2 ^ 31 | SLeave => FI (snd b) end));
      [| intros a Ha; exact Ha | exact HF].
    intros a Ha. pose proof (dispatch_fi a Ha) as D. destruct (dispatch ivar_ref flush a) as [u w'|w'|rc w']; cbn [fst snd].
    - exact D.
    - exact D.
    - exact D.
  Qed.
End LoopI.
