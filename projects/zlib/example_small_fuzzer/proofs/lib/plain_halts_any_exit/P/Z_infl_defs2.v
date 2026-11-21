(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArmLib.

Module Z_infl_loop.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2.
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

Ltac disp_case HARM HDISP EM :=
  rewrite (HDISP _ EM); rewrite EM;
  match goal with |- context [wz ?M] => first [unfold M] end;
  do 2 zs; if_true; do 6 zs;
  eapply HARM; [ eassumption | eapply ILOOP_intro; try reflexivity; eassumption | eassumption | eassumption | eassumption | eassumption | exact EM ].

Lemma dispatch_spec : forall X w x8 ms,
  ix_flush X = flush -> ILOOP X w PC_DISPATCH x8 (wz (is_mode (w_s w))) ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w ->
  evt psegs (fun ms' => IPOST X (dispatch ivar_ref flush w) ms' /\ PATI X (wof (dispatch ivar_ref flush w))) ms.
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
            /\ WINV (snd res) /\ ATY (w_s (snd res)) /\ PATI X (snd res).

Definition lstep (w : iw) : iw + (istop * iw) :=
  match dispatch ivar_ref flush w with
  | ARun _ w' => inl w'
  | ALeave w' => inr (SLeave, w')
  | ARet rc w' => inr (SRet rc, w')
  end.

Lemma inf_loop_n : forall (k : nat) n X w x8 ms, Z.to_nat n = k ->
  ix_flush X = flush -> ILOOP X w PC_DISPATCH x8 (wz (is_mode (w_s w))) ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w -> PHI w < n ->
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
  ix_flush X = flush -> ILOOP X w PC_DISPATCH x8 (wz (is_mode (w_s w))) ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w ->
  PHI w < 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64) ->
  evt psegs (LPOST X (inf_loop ivar_ref flush w)) ms.
Proof.
  intros X w x8 ms EF HL XO HW HA HP HPHI. unfold inf_loop.
  exact (inf_loop_n _ _ X w x8 ms eq_refl EF HL XO HW HA HP HPHI).
Qed.
End Loop.
End Z_infl_loop.

Module Z_infl_arms.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_ikit Z_infl_defs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_defs2.Z_infl_loop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

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

Lemma inf_loop_of_arms : forall flush, arms_ok flush -> forall X w x8 ms,
  ix_flush X = flush -> ILOOP X w PC_DISPATCH x8 (Z_to_bv 64 (is_mode (w_s w))) ms -> ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w ->
  PHI w < 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64) ->
  evt psegs (LPOST X (inf_loop ivar_ref flush w)) ms.
Proof.
  intros flush [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23].
  exact (inf_loop_spec flush H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23).
Qed.
End Z_infl_arms.

Module Z_infl_pro.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma inflate_prologue : forall (X : ictx) (s : inflate_state) (zc : ZCall)
         (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
  ix_m0 X = m -> ix_ok X ->
  izs m (ix_L X) (icall_of_zcall zc) -> IST m (ix_L X) s -> iin m X -> iout m (ix_L X) (ix_rest0 X) (icall_of_zcall zc) 0 ->
  stk psegs m (ix_lo X) (bv_unsigned (ix_sp X)) -> mem_inv psegs m ->
  (is_window_blk s <> None -> ix_hasw X = true) ->
  HEAD <= is_mode s <= SYNC -> 0 <= is_bits s < 64 -> 0 <= is_hold s < 2^64 ->
  0 <= zlength (zc_input zc) <= 1 -> 0 <= zc_avail_out zc <= 1 -> 0 <= ix_flush X <= 4 ->
  0 < il_NI (ix_L X) < 2^63 -> 0 < il_NO (ix_L X) < 2^63 ->
  evt psegs (fun ms' => exists x8, ILOOP X (W0 s zc) PC_DISPATCH x8 (wz (is_mode (w_s (W0 s zc)))) ms')
      (MS (mkR (ix_ra X) (ix_sp X) (ix_gp X) (ix_tp X) t0 t1 t2 (ix_s0 X) (ix_s1 X) (wz (il_S (ix_L X))) (wz (ix_flush X)) a2 a3 a4 a5 a6 a7
               (ix_s2 X) (ix_s3 X) (ix_s4 X) (ix_s5 X) (ix_s6 X) (ix_s7 X) (ix_s8 X) (ix_s9 X) (ix_s10 X) (ix_s11 X) t3 t4 t5 t6)
          (ix_F X) (wz Z_INFLATE) (ix_fc X) None m (seg_rom psegs)).
Proof.
  intros X s zc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m EM0 XO ZS ST IN OUT STK MI HWIN RM RB RH RAI RAO RF RNI RNO.
  unfold Z_INFLATE, HEAD, SYNC in *. ix_open XO.
  pose proof (munch_refl (ix_W X) m) as MU. unfold ix_W in MU. pose proof (wmono_refl psegs m) as WM.
  unfold iin in IN. unfold iout in OUT.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) (icall_of_zcall zc) 0 ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_izs ZS. cbn [icall_of_zcall ic_next_in ic_avail_in ic_total_in ic_next_out ic_avail_out ic_total_out ic_msg ic_adler] in ZS.
  open_IST ST. open_isA GA.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168)] m) as MUf. pose proof (wmono_refl psegs m) as WMf.
  carve_frame 224%nat STK.
  do 16 zs. br_true. do 2 zs. br_true. do 2 zs. br_true. do 2 zs. br_true. do 2 zs. br_true.
  do 6 zs. rewrite (swrap32_sub _ 16180) by (try reflexivity; lia).
  br_true. do 2 zs. br_true. do 2 zs. br_false. do 6 zs.
  br_cases KT.
  -
    do 32 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists.
    assert (ES : s_entry s = s) by (unfold s_entry; replace (is_mode s =? TYPE) with false by (symmetry; apply Z.eqb_neq; unfold TYPE; lia); reflexivity).
    unfold W0. rewrite ES. cbn [w_s].
    eapply ILOOP_intro; ired; [ireg .. |].
    apply IMEM_intro; ired.
    + eexists. unfold iframe_cells. ired. exact FR.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app icall_of_zcall]. ired. exact ZS.
    + constructor; [unfold isA, isA_cells; exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + rewrite EM0. exact MU.
    + rewrite EM0. exact WM.
  -
    do 3 zs. do 32 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists.
    assert (ES : s_entry s = iset_mode s TYPEDO) by (unfold s_entry; replace (is_mode s =? TYPE) with true by (symmetry; apply Z.eqb_eq; unfold TYPE; lia); reflexivity).
    unfold W0. rewrite ES. cbn [w_s].
    eapply ILOOP_intro; ired; [ireg .. |].
    apply IMEM_intro; ired.
    + eexists. unfold iframe_cells. ired. exact FR.
    + exact STK.
    + eexists _, _, _, _, _. unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE. cbn [app icall_of_zcall]. ired. exact ZS.
    + constructor; ired; [unfold isA, isA_cells; ired; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + unfold iout. exact OUT.
    + eassumption.
    + rewrite EM0. exact MU.
    + rewrite EM0. exact WM.
Qed.
End Z_infl_pro.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Record iscr : Type := mkSC {
  sc5 : word; sc6 : word; sc7 : word; sc8 : word; sc12 : word; sc13 : word; sc14 : word; sc15 : word; sc16 : word; sc17 : word;
  sc26 : word; sc27 : word; sc28 : word; sc30 : word }.

Definition ILOOPg (X : ictx) (w : iw) (pc : Z) (q : iscr) : machine_state -> Prop :=
  fun ms => exists m,
    ms = MS (mkR (wz (ir_left (w_r w))) (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) (sc5 q) (sc6 q) (sc7 q) (wz (il_As (ix_L X)))
                 (sc8 q) (wz (il_S (ix_L X))) (wz (ix_flush X)) (sc12 q) (sc13 q) (sc14 q) (sc15 q) (sc16 q) (sc17 q)
                 (wz (ir_have (w_r w))) (wz (il_NO (ix_L X) + ir_put (w_r w))) (wz 16209) (wz (-2))
                 (wz (il_As (ix_L X) + 168)) (wz (ir_hold (w_r w))) (wz (ir_bits (w_r w))) (wz 74976)
                 (sc27 q) (sc26 q) (sc28 q) (wz 30) (sc30 q) (wz (-16180)))
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom psegs)
    /\ IMEM X w m.

Lemma ILOOPg_intro : forall X w pc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x1 = wz (ir_left (w_r w)) -> x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X ->
  x9 = wz (ir_have (w_r w)) -> x10 = wz (il_S (ix_L X)) -> x11 = wz (ix_flush X) ->
  x18 = wz (il_NO (ix_L X) + ir_put (w_r w)) -> x19 = wz 16209 -> x20 = wz (-2) -> x21 = wz (il_As (ix_L X) + 168) ->
  x22 = wz (ir_hold (w_r w)) -> x23 = wz (ir_bits (w_r w)) -> x24 = wz 74976 -> x25 = wz (il_As (ix_L X)) ->
  x29 = wz 30 -> x31 = wz (-16180) -> F = ix_F X -> fc = ix_fc X ->
  IMEM X w m ->
  ILOOPg X w pc (mkSC x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30)
         (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
             F (wz pc) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold ILOOPg. eexists. split; [reflexivity| assumption]. Qed.

Lemma ILOOPg_of_ILOOP : forall X w pc x8 x12 ms, ILOOP X w pc x8 x12 ms ->
  exists q, ILOOPg X w pc q ms /\ sc8 q = x8 /\ sc12 q = x12 /\ sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)).
Proof.
  intros X w pc x8 x12 ms (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HM).
  exists (mkSC x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 (wz (il_NI (ix_L X) + ir_next (w_r w))) x27 x28 x30).
  split; [|repeat split]. exists m. split; [reflexivity| exact HM].
Qed.
Lemma ILOOPg_of_ILOOP27 : forall X w pc x8 x12 x26 ms, ILOOP27 X w pc x8 x12 x26 ms ->
  exists q, ILOOPg X w pc q ms /\ sc8 q = x8 /\ sc12 q = x12 /\ sc26 q = x26 /\ sc27 q = wz (il_NI (ix_L X) + ir_next (w_r w)).
Proof.
  intros X w pc x8 x12 x26 ms (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x30 & m & -> & HM).
  exists (mkSC x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 (wz (il_NI (ix_L X) + ir_next (w_r w))) x28 x30).
  split; [|repeat split]. exists m. split; [reflexivity| exact HM].
Qed.
Lemma ILOOP_of_ILOOPg : forall X w pc q ms, ILOOPg X w pc q ms -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ILOOP X w pc (sc8 q) (sc12 q) ms.
Proof. intros X w pc [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms (m & -> & HM) E. cbn [sc26 sc8 sc12] in *. subst x26. unfold ILOOP. do 12 eexists. split; [reflexivity| exact HM]. Qed.
Lemma ILOOP27_of_ILOOPg : forall X w pc q ms, ILOOPg X w pc q ms -> sc27 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ILOOP27 X w pc (sc8 q) (sc12 q) (sc26 q) ms.
Proof. intros X w pc [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms (m & -> & HM) E. cbn [sc27 sc26 sc8 sc12] in *. subst x27. unfold ILOOP27. do 11 eexists. split; [reflexivity| exact HM]. Qed.

Ltac iarm_openg HL :=
  let m := fresh "m" in let jf := fresh "jf" in
  let FRM := fresh "FRM" in let STK := fresh "STK" in let ZS := fresh "ZS" in let ST := fresh "ST" in let IN := fresh "IN" in
  let OUT := fresh "OUT" in let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in
  destruct HL as (m & -> & (jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM);
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *.

Definition NBJg (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (n : Z) (pcj : Z) (Q : iregs -> iscr -> Prop) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 q, NEEDBITS n (mkW s c r) = ARun tt (mkW s c r1)
                  /\ ((r1 = r /\ n <= ir_bits r) \/ (r1 = pullr c r /\ 0 < ir_have r /\ ir_bits r < n <= ir_bits r + 8))
                  /\ ILOOPg X (mkW s c r1) pcj q ms' /\ Q r1 q)
    \/ (exists r1, NEEDBITS n (mkW s c r) = ALeave (mkW s c r1) /\ (r1 = r \/ r1 = pullr c r) /\ ILEAVE X (mkW s c r1) ms').

#[local] Transparent iout_bytes.
Lemma iout_bytes_nth : forall rest0 c put i, 0 <= i < put ->
  nth_error (iout_bytes rest0 c put) (Z.to_nat i) = Some (Z_to_bv 8 (arr_get (ic_outbuf c) i)).
Proof. intros rest0 c put i Hi. unfold iout_bytes. rewrite nth_error_app1 by (rewrite av8_length; lia). apply av8_nth. lia. Qed.
Lemma iout_bytes_ext : forall rest0 c' c put, ic_outbuf c' = ic_outbuf c -> iout_bytes rest0 c' put = iout_bytes rest0 c put.
Proof. intros rest0 c' c put E. unfold iout_bytes. rewrite E. reflexivity. Qed.
#[local] Opaque iout_bytes.

Lemma firstn1_skipn_nth : forall {A} (l : list A) k b, nth_error l k = Some b -> firstn 1 (skipn k l) = [b].
Proof.
  intros A l. induction l as [|x l IH]; intros k b H; destruct k; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

Lemma iout_byte_at : forall m L rest0 c put i, iout m L rest0 c put -> 0 <= i < put -> put <= Z.of_nat (length rest0) ->
  bytes_at psegs m (il_NO L + i) [Z_to_bv 8 (arr_get (ic_outbuf c) i)].
Proof.
  intros m L rest0 c put i H Hi Hp. unfold iout in H.
  pose proof (iout_bytes_nth rest0 c put i Hi) as HN.
  pose proof (u8arr_sub_bytes m _ _ (Z.to_nat i) 1%nat H) as HB.
  rewrite (firstn1_skipn_nth _ _ _ HN) in HB. replace (Z.of_nat (Z.to_nat i)) with i in HB by lia. apply HB.
  pose proof (nth_error_lt _ _ _ HN). lia.
Qed.
