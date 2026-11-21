(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs Zg_infl_defs.
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

Hypothesis A_HEAD : arm_stmtg flush HEAD PC_HEAD (arm_HEAD ivar_ref).
Hypothesis A_DICTID : arm_stmtg flush DICTID PC_DICTID (arm_DICTID ivar_ref flush).
Hypothesis A_DICT : arm_stmtg flush DICT PC_DICT (arm_DICT ivar_ref flush).
Hypothesis A_TYPE : arm_stmtg flush TYPE PC_TYPE (arm_TYPE ivar_ref flush).
Hypothesis A_TYPEDO : arm_stmtg flush TYPEDO PC_TYPEDO (arm_TYPEDO ivar_ref flush).
Hypothesis A_STORED : arm_stmtg flush STORED PC_STORED (arm_STORED ivar_ref flush).
Hypothesis A_COPY_ : arm_stmtg flush COPY_ PC_COPY_ arm_COPY_.
Hypothesis A_COPY : arm_stmtg flush COPY PC_COPY arm_COPY.
Hypothesis A_TABLE : arm_stmtg flush TABLE PC_TABLE (arm_TABLE ivar_ref flush).
Hypothesis A_LENLENS : arm_stmtg flush LENLENS PC_LENLENS (arm_LENLENS ivar_ref flush).
Hypothesis A_CODELENS : arm_stmtg flush CODELENS PC_CODELENS (arm_CODELENS ivar_ref flush).
Hypothesis A_LEN_ : arm_stmtg flush LEN_ PC_LEN_ (arm_LEN_ ivar_ref).
Hypothesis A_LEN : arm_stmtg flush LEN PC_LEN (arm_LEN ivar_ref).
Hypothesis A_LENEXT : arm_stmtg flush LENEXT PC_LENEXT (arm_LENEXT ivar_ref).
Hypothesis A_DIST : arm_stmtg flush DIST PC_DIST (arm_DIST ivar_ref).
Hypothesis A_DISTEXT : arm_stmtg flush DISTEXT PC_DISTEXT (arm_DISTEXT ivar_ref).
Hypothesis A_MATCH : arm_stmtg flush MATCH PC_MATCH (arm_MATCH ivar_ref).
Hypothesis A_LIT : arm_stmtg flush LIT PC_LIT arm_LIT.
Hypothesis A_CHECK : arm_stmtg flush CHECK PC_CHECK arm_CHECK.
Hypothesis A_LENGTH : arm_stmtg flush LENGTH PC_LENGTH arm_LENGTH.
Hypothesis A_DONE : arm_stmtg flush DONE PC_DONE arm_DONE.
Hypothesis A_BAD : arm_stmtg flush BAD PC_BAD arm_BAD.
Hypothesis A_MEM : arm_stmtg flush MEM PC_MEM arm_MEM.

Ltac disp_case HARM HDISP EM :=
  rewrite (HDISP _ EM); rewrite EM;
  match goal with |- context [wz ?M] => first [unfold M] end;
  do 2 zs; if_true; do 6 zs;
  eapply HARM; [ eassumption | eapply ILOOP_intro; try reflexivity; eassumption | eassumption | eassumption | eassumption | eassumption | exact EM ].

Lemma dispatch_spec : forall X w x8 ms,
  ix_flush X = flush -> ILOOP X w PC_DISPATCH x8 (wz (is_mode (w_s w))) ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w ->
  evt psegs (fun ms' => IPOST X (dispatch ivar_ref flush w) ms' /\ PATG X (wof (dispatch ivar_ref flush w))) ms.
Proof.
  intros X w x8 ms EF HL XO HW HA HP.
  assert (RM : HEAD <= is_mode (w_s w) <= MEM).
  { destruct w as [s c r]. destruct HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in *. exact (MF_mode_range _ _ _ _ HMF). }
  assert (NG : ~ (FLAGS <= is_mode (w_s w) <= HCRC)) by (destruct HP as (_ & _ & _ & _ & H & _); exact H).
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM).
  assert (MI : mem_inv psegs m) by (destruct HMEM as (_ & _ & _ & _ & _ & H & _); exact H).
  unfold PC_DISPATCH.
  destruct (mode_cases _ RM NG) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]].
  - disp_case A_HEAD disp_HEAD E.
  - disp_case A_DICTID disp_DICTID E.
  - disp_case A_DICT disp_DICT E.
  - disp_case A_TYPE disp_TYPE E.
  - disp_case A_TYPEDO disp_TYPEDO E.
  - disp_case A_STORED disp_STORED E.
  - disp_case A_COPY_ disp_COPY_ E.
  - disp_case A_COPY disp_COPY E.
  - disp_case A_TABLE disp_TABLE E.
  - disp_case A_LENLENS disp_LENLENS E.
  - disp_case A_CODELENS disp_CODELENS E.
  - disp_case A_LEN_ disp_LEN_ E.
  - disp_case A_LEN disp_LEN E.
  - disp_case A_LENEXT disp_LENEXT E.
  - disp_case A_DIST disp_DIST E.
  - disp_case A_DISTEXT disp_DISTEXT E.
  - disp_case A_MATCH disp_MATCH E.
  - disp_case A_LIT disp_LIT E.
  - disp_case A_CHECK disp_CHECK E.
  - disp_case A_LENGTH disp_LENGTH E.
  - disp_case A_DONE disp_DONE E.
  - disp_case A_BAD disp_BAD E.
  - disp_case A_MEM disp_MEM E.
Qed.

Definition LPOST (X : ictx) (res : istop * iw) : machine_state -> Prop :=
  fun ms => (match fst res with SLeave => ILEAVE X (snd res) ms | SRet rc => IRET X rc (snd res) ms end)
            /\ WINV (snd res) /\ ATY (w_s (snd res)) /\ PATG X (snd res).

Definition lstep (w : iw) : iw + (istop * iw) :=
  match dispatch ivar_ref flush w with
  | ARun _ w' => inl w'
  | ALeave w' => inr (SLeave, w')
  | ARet rc w' => inr (SRet rc, w')
  end.

Lemma inf_loop_n : forall (k : nat) n X w x8 ms, Z.to_nat n = k ->
  ix_flush X = flush -> ILOOP X w PC_DISPATCH x8 (wz (is_mode (w_s w))) ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w -> PHI w < n ->
  evt psegs (LPOST X (iterZ n lstep (fun w => (SLeave, w)) w)) ms.
Proof.
  induction k as [|k IH]; intros n X w x8 ms Ek EF HL XO HW HA HP HPHI.
  - exfalso. pose proof (PHI_nonneg w HW). lia.
  - rewrite iterZ_step by lia.
    eapply evt_cut; [exact (dispatch_spec X w x8 ms EF HL XO HW HA HP)|].
    intros ms' (HPOST & HPAT).
    destruct w as [s c r].
    pose proof (dispatch_safe flush (mkW s c r) s c r HW (Z.le_refl _)) as HS.
    pose proof (dispatch_aty ivar_ref flush (mkW s c r) HA) as HA'.
    unfold lstep. destruct (dispatch ivar_ref flush (mkW s c r)) as [[] w' | w' | rc w'] eqn:ED; cbn [POST ATYr wof IPOST] in *.
    + destruct HS as [HW' HLT]. destruct HPOST as (x8' & HL').
      apply (IH (n - 1) X w' x8' ms'); [lia| exact EF| exact HL'| exact XO| exact HW'| exact HA'| exact HPAT| lia].
    + apply evt_done. unfold LPOST. cbn [fst snd]. repeat (split; [assumption|]). assumption.
    + destruct HS as [HW' _]. apply evt_done. unfold LPOST. cbn [fst snd]. repeat (split; [assumption|]). assumption.
Qed.

Theorem inf_loop_spec : forall X w x8 ms,
  ix_flush X = flush -> ILOOP X w PC_DISPATCH x8 (wz (is_mode (w_s w))) ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATG X w ->
  PHI w < 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64) ->
  evt psegs (LPOST X (inf_loop ivar_ref flush w)) ms.
Proof.
  intros X w x8 ms EF HL XO HW HA HP HPHI. unfold inf_loop.
  exact (inf_loop_n _ _ X w x8 ms eq_refl EF HL XO HW HA HP HPHI).
Qed.
End Loop.
