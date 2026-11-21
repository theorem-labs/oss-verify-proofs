(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs.

Module Z_infl_loop.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
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

Ltac disp_case HARM HDISP EM M GA HMEM :=
  rewrite (HDISP _ EM); rewrite EM in GA; unfold M in GA;
  do 5 zs; br_true; do 7 zs;
  eapply HARM; [ eassumption | eapply ILOOP_intro; try reflexivity; exact HMEM | eassumption | eassumption | eassumption | eassumption | exact EM ].

Lemma dispatch_spec : forall X w x26 x12 ms,
  ix_flush X = flush -> ILOOP X w PC_DISPATCH x26 x12 ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w ->
  evt usegs (fun ms' => IPOST X (dispatch ivar_ref flush w) ms' /\ PATI X (wof (dispatch ivar_ref flush w))) ms.
Proof.
  intros X w x26 x12 ms EF HL XO HW HA HP.
  assert (RM : HEAD <= is_mode (w_s w) <= MEM).
  { destruct w as [s c r]. destruct HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in *. exact (MF_mode_range _ _ _ _ HMF). }
  assert (NG : ~ (FLAGS <= is_mode (w_s w) <= HCRC)) by (destruct HP as (_ & _ & _ & _ & H & _); exact H).
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM).
  pose proof HMEM as ((j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM). unfold iframe_cells in FRM.
  ix_open XO. open_IST ST. open_isA GA.
  unfold PC_DISPATCH.
  destruct (mode_cases _ RM NG) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]].
  - disp_case A_HEAD disp_HEAD E HEAD GA HMEM.
  - disp_case A_DICTID disp_DICTID E DICTID GA HMEM.
  - disp_case A_DICT disp_DICT E DICT GA HMEM.
  - disp_case A_TYPE disp_TYPE E TYPE GA HMEM.
  - disp_case A_TYPEDO disp_TYPEDO E TYPEDO GA HMEM.
  - disp_case A_STORED disp_STORED E STORED GA HMEM.
  - disp_case A_COPY_ disp_COPY_ E COPY_ GA HMEM.
  - disp_case A_COPY disp_COPY E COPY GA HMEM.
  - disp_case A_TABLE disp_TABLE E TABLE GA HMEM.
  - disp_case A_LENLENS disp_LENLENS E LENLENS GA HMEM.
  - disp_case A_CODELENS disp_CODELENS E CODELENS GA HMEM.
  - disp_case A_LEN_ disp_LEN_ E LEN_ GA HMEM.
  - disp_case A_LEN disp_LEN E LEN GA HMEM.
  - disp_case A_LENEXT disp_LENEXT E LENEXT GA HMEM.
  - disp_case A_DIST disp_DIST E DIST GA HMEM.
  - disp_case A_DISTEXT disp_DISTEXT E DISTEXT GA HMEM.
  - disp_case A_MATCH disp_MATCH E MATCH GA HMEM.
  - disp_case A_LIT disp_LIT E LIT GA HMEM.
  - disp_case A_CHECK disp_CHECK E CHECK GA HMEM.
  - disp_case A_LENGTH disp_LENGTH E LENGTH GA HMEM.
  - disp_case A_DONE disp_DONE E DONE GA HMEM.
  - disp_case A_BAD disp_BAD E BAD GA HMEM.
  - disp_case A_MEM disp_MEM E MEM GA HMEM.
Qed.

Definition LPOST (X : ictx) (res : istop * iw) : machine_state -> Prop :=
  fun ms => (match fst res with SLeave => ILEAVE X (snd res) ms | SRet rc => IRET X rc (snd res) ms end)
            /\ WINV (snd res) /\ ATY (w_s (snd res)) /\ PATI X (snd res).

Definition lstep (w : iw) : iw + (istop * iw) :=
  match dispatch ivar_ref flush w with
  | ARun _ w' => inl w'
  | ALeave w' => inr (SLeave, w')
  | ARet rc w' => inr (SRet rc, w')
  end.

Lemma inf_loop_n : forall (k : nat) n X w x26 x12 ms, Z.to_nat n = k ->
  ix_flush X = flush -> ILOOP X w PC_DISPATCH x26 x12 ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w -> PHI w < n ->
  evt usegs (LPOST X (iterZ n lstep (fun w => (SLeave, w)) w)) ms.
Proof.
  induction k as [|k IH]; intros n X w x26 x12 ms Ek EF HL XO HW HA HP HPHI.
  - exfalso. pose proof (PHI_nonneg w HW). lia.
  - rewrite iterZ_step by lia.
    eapply evt_cut; [exact (dispatch_spec X w x26 x12 ms EF HL XO HW HA HP)|].
    intros ms' (HPOST & HPAT).
    destruct w as [s c r].
    pose proof (dispatch_safe flush (mkW s c r) s c r HW (Z.le_refl _)) as HS.
    pose proof (dispatch_aty ivar_ref flush (mkW s c r) HA) as HA'.
    unfold lstep. destruct (dispatch ivar_ref flush (mkW s c r)) as [[] w' | w' | rc w'] eqn:ED; cbn [POST ATYr wof IPOST] in *.
    + destruct HS as [HW' HLT]. destruct HPOST as (x26' & x12' & HL').
      apply (IH (n - 1) X w' x26' x12' ms'); [lia| exact EF| exact HL'| exact XO| exact HW'| exact HA'| exact HPAT| lia].
    + apply evt_done. unfold LPOST. cbn [fst snd]. repeat (split; [assumption|]). assumption.
    + destruct HS as [HW' _]. apply evt_done. unfold LPOST. cbn [fst snd]. repeat (split; [assumption|]). assumption.
Qed.

Theorem inf_loop_spec : forall X w x26 x12 ms,
  ix_flush X = flush -> ILOOP X w PC_DISPATCH x26 x12 ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w ->
  PHI w < 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64) ->
  evt usegs (LPOST X (inf_loop ivar_ref flush w)) ms.
Proof.
  intros X w x26 x12 ms EF HL XO HW HA HP HPHI. unfold inf_loop.
  exact (inf_loop_n _ _ X w x26 x12 ms eq_refl EF HL XO HW HA HP HPHI).
Qed.
End Loop.
End Z_infl_loop.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_arms.Z_infl_loop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record arms_ok (flush : Z) : Prop := mkArms {
  a_HEAD : arm_stmt flush HEAD PC_HEAD (arm_HEAD ivar_ref);
  a_DICTID : arm_stmt flush DICTID PC_DICTID (arm_DICTID ivar_ref flush);
  a_DICT : arm_stmt flush DICT PC_DICT (arm_DICT ivar_ref flush);
  a_TYPE : arm_stmt flush TYPE PC_TYPE (arm_TYPE ivar_ref flush);
  a_TYPEDO : arm_stmt flush TYPEDO PC_TYPEDO (arm_TYPEDO ivar_ref flush);
  a_STORED : arm_stmt flush STORED PC_STORED (arm_STORED ivar_ref flush);
  a_COPY_ : arm_stmt flush COPY_ PC_COPY_ arm_COPY_;
  a_COPY : arm_stmt flush COPY PC_COPY arm_COPY;
  a_TABLE : arm_stmt flush TABLE PC_TABLE (arm_TABLE ivar_ref flush);
  a_LENLENS : arm_stmt flush LENLENS PC_LENLENS (arm_LENLENS ivar_ref flush);
  a_CODELENS : arm_stmt flush CODELENS PC_CODELENS (arm_CODELENS ivar_ref flush);
  a_LEN_ : arm_stmt flush LEN_ PC_LEN_ (arm_LEN_ ivar_ref);
  a_LEN : arm_stmt flush LEN PC_LEN (arm_LEN ivar_ref);
  a_LENEXT : arm_stmt flush LENEXT PC_LENEXT (arm_LENEXT ivar_ref);
  a_DIST : arm_stmt flush DIST PC_DIST (arm_DIST ivar_ref);
  a_DISTEXT : arm_stmt flush DISTEXT PC_DISTEXT (arm_DISTEXT ivar_ref);
  a_MATCH : arm_stmt flush MATCH PC_MATCH (arm_MATCH ivar_ref);
  a_LIT : arm_stmt flush LIT PC_LIT arm_LIT;
  a_CHECK : arm_stmt flush CHECK PC_CHECK arm_CHECK;
  a_LENGTH : arm_stmt flush LENGTH PC_LENGTH arm_LENGTH;
  a_DONE : arm_stmt flush DONE PC_DONE arm_DONE;
  a_BAD : arm_stmt flush BAD PC_BAD arm_BAD;
  a_MEM : arm_stmt flush MEM PC_MEM arm_MEM
}.

Lemma inf_loop_of_arms : forall flush, arms_ok flush -> forall X w x26 x12 ms,
  ix_flush X = flush -> ILOOP X w PC_DISPATCH x26 x12 ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w ->
  PHI w < 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64) ->
  evt usegs (LPOST X (inf_loop ivar_ref flush w)) ms.
Proof.
  intros flush [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23].
  exact (inf_loop_spec flush H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23).
Qed.
