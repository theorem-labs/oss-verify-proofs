(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateSafeS1 RefInflateSafeS2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma mode_cases : forall m, HEAD <= m <= MEM -> ~ (FLAGS <= m <= HCRC) ->
  m = HEAD \/ m = DICTID \/ m = DICT \/ m = TYPE \/ m = TYPEDO \/ m = STORED \/ m = COPY_ \/ m = COPY \/ m = TABLE \/ m = LENLENS
  \/ m = CODELENS \/ m = LEN_ \/ m = LEN \/ m = LENEXT \/ m = DIST \/ m = DISTEXT \/ m = MATCH \/ m = LIT \/ m = CHECK \/ m = LENGTH
  \/ m = DONE \/ m = BAD \/ m = MEM.
Proof.
  intros m H N. unfold HEAD, MEM, FLAGS, HCRC, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
    DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD in *. lia.
Qed.

Section Loop.
Variable flush : Z.

Ltac disp_at := intros [s c r] H; cbn [w_s] in H; unfold dispatch, abind, gs; cbn [w_s]; rewrite H; reflexivity.
Lemma disp_HEAD : forall w, is_mode (w_s w) = HEAD -> dispatch ivar_ref flush w = arm_HEAD ivar_ref w. Proof. disp_at. Qed.
Lemma disp_DICTID : forall w, is_mode (w_s w) = DICTID -> dispatch ivar_ref flush w = arm_DICTID ivar_ref flush w. Proof. disp_at. Qed.
Lemma disp_DICT : forall w, is_mode (w_s w) = DICT -> dispatch ivar_ref flush w = arm_DICT ivar_ref flush w. Proof. disp_at. Qed.
Lemma disp_TYPE : forall w, is_mode (w_s w) = TYPE -> dispatch ivar_ref flush w = arm_TYPE ivar_ref flush w. Proof. disp_at. Qed.
Lemma disp_TYPEDO : forall w, is_mode (w_s w) = TYPEDO -> dispatch ivar_ref flush w = arm_TYPEDO ivar_ref flush w. Proof. disp_at. Qed.
Lemma disp_STORED : forall w, is_mode (w_s w) = STORED -> dispatch ivar_ref flush w = arm_STORED ivar_ref flush w. Proof. disp_at. Qed.
Lemma disp_COPY_ : forall w, is_mode (w_s w) = COPY_ -> dispatch ivar_ref flush w = arm_COPY_ w. Proof. disp_at. Qed.
Lemma disp_COPY : forall w, is_mode (w_s w) = COPY -> dispatch ivar_ref flush w = arm_COPY w. Proof. disp_at. Qed.
Lemma disp_TABLE : forall w, is_mode (w_s w) = TABLE -> dispatch ivar_ref flush w = arm_TABLE ivar_ref flush w. Proof. disp_at. Qed.
Lemma disp_LENLENS : forall w, is_mode (w_s w) = LENLENS -> dispatch ivar_ref flush w = arm_LENLENS ivar_ref flush w. Proof. disp_at. Qed.
Lemma disp_CODELENS : forall w, is_mode (w_s w) = CODELENS -> dispatch ivar_ref flush w = arm_CODELENS ivar_ref flush w. Proof. disp_at. Qed.
Lemma disp_LEN_ : forall w, is_mode (w_s w) = LEN_ -> dispatch ivar_ref flush w = arm_LEN_ ivar_ref w. Proof. disp_at. Qed.
Lemma disp_LEN : forall w, is_mode (w_s w) = LEN -> dispatch ivar_ref flush w = arm_LEN ivar_ref w. Proof. disp_at. Qed.
Lemma disp_LENEXT : forall w, is_mode (w_s w) = LENEXT -> dispatch ivar_ref flush w = arm_LENEXT ivar_ref w. Proof. disp_at. Qed.
Lemma disp_DIST : forall w, is_mode (w_s w) = DIST -> dispatch ivar_ref flush w = arm_DIST ivar_ref w. Proof. disp_at. Qed.
Lemma disp_DISTEXT : forall w, is_mode (w_s w) = DISTEXT -> dispatch ivar_ref flush w = arm_DISTEXT ivar_ref w. Proof. disp_at. Qed.
Lemma disp_MATCH : forall w, is_mode (w_s w) = MATCH -> dispatch ivar_ref flush w = arm_MATCH ivar_ref w. Proof. disp_at. Qed.
Lemma disp_LIT : forall w, is_mode (w_s w) = LIT -> dispatch ivar_ref flush w = arm_LIT w. Proof. disp_at. Qed.
Lemma disp_CHECK : forall w, is_mode (w_s w) = CHECK -> dispatch ivar_ref flush w = arm_CHECK w. Proof. disp_at. Qed.
Lemma disp_LENGTH : forall w, is_mode (w_s w) = LENGTH -> dispatch ivar_ref flush w = arm_LENGTH w. Proof. disp_at. Qed.
Lemma disp_DONE : forall w, is_mode (w_s w) = DONE -> dispatch ivar_ref flush w = arm_DONE w. Proof. disp_at. Qed.
Lemma disp_BAD : forall w, is_mode (w_s w) = BAD -> dispatch ivar_ref flush w = arm_BAD w. Proof. disp_at. Qed.
Lemma disp_MEM : forall w, is_mode (w_s w) = MEM -> dispatch ivar_ref flush w = arm_MEM w. Proof. disp_at. Qed.

Hypothesis A_HEAD : arm_stmt flush HEAD PC_HEAD (arm_HEAD ivar_ref).
Hypothesis A_DICTID : arm_stmt flush DICTID PC_DICTID (arm_DICTID ivar_ref flush).
Hypothesis A_DICT : arm_stmt flush DICT PC_DICT (arm_DICT ivar_ref flush).
Hypothesis A_TYPE : arm_stmt flush TYPE PC_TYPE (arm_TYPE ivar_ref flush).
Hypothesis A_TYPEDO : arm_stmt flush TYPEDO PC_TYPEDO (arm_TYPEDO ivar_ref flush).
Hypothesis A_STORED : arm_stmt flush STORED PC_STORED (arm_STORED ivar_ref flush).
Hypothesis A_COPY_ : arm_stmt flush COPY_ PC_COPY_ arm_COPY_.
Hypothesis A_COPY : arm_stmt flush COPY PC_COPY arm_COPY.
Hypothesis A_TABLE : arm_stmt flush TABLE PC_TABLE (arm_TABLE ivar_ref flush).
Hypothesis A_LENLENS : arm_stmt flush LENLENS PC_LENLENS (arm_LENLENS ivar_ref flush).
Hypothesis A_CODELENS : arm_stmt flush CODELENS PC_CODELENS (arm_CODELENS ivar_ref flush).
Hypothesis A_LEN_ : arm_stmt flush LEN_ PC_LEN_ (arm_LEN_ ivar_ref).
Hypothesis A_LEN : arm_stmt flush LEN PC_LEN (arm_LEN ivar_ref).
Hypothesis A_LENEXT : arm_stmt flush LENEXT PC_LENEXT (arm_LENEXT ivar_ref).
Hypothesis A_DIST : arm_stmt flush DIST PC_DIST (arm_DIST ivar_ref).
Hypothesis A_DISTEXT : arm_stmt flush DISTEXT PC_DISTEXT (arm_DISTEXT ivar_ref).
Hypothesis A_MATCH : arm_stmt flush MATCH PC_MATCH (arm_MATCH ivar_ref).
Hypothesis A_LIT : arm_stmt flush LIT PC_LIT arm_LIT.
Hypothesis A_CHECK : arm_stmt flush CHECK PC_CHECK arm_CHECK.
Hypothesis A_LENGTH : arm_stmt flush LENGTH PC_LENGTH arm_LENGTH.
Hypothesis A_DONE : arm_stmt flush DONE PC_DONE arm_DONE.
Hypothesis A_BAD : arm_stmt flush BAD PC_BAD arm_BAD.
Hypothesis A_MEM : arm_stmt flush MEM PC_MEM arm_MEM.

Ltac disp_case HARM HDISP EM :=
  rewrite (HDISP _ EM); rewrite EM;
  match goal with |- context [wz ?M] => first [unfold M] end;
  do 2 zs; if_true; do 6 zs;
  eapply HARM; [ eassumption | eapply ILOOP_intro; try reflexivity; eassumption | eassumption | eassumption | eassumption | eassumption | exact EM ].

Definition LPOST (X : ictx) (res : istop * iw) : machine_state -> Prop :=
  fun ms => (match fst res with SLeave => ILEAVE X (snd res) ms | SRet rc => IRET X rc (snd res) ms end)
            /\ WINV (snd res) /\ ATY (w_s (snd res)) /\ PATI X (snd res).

Definition lstep (w : iw) : iw + (istop * iw) :=
  match dispatch ivar_ref flush w with
  | ARun _ w' => inl w'
  | ALeave w' => inr (SLeave, w')
  | ARet rc w' => inr (SRet rc, w')
  end.

End Loop.
