(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad MSafe Stdio SjModel PjModel ImpModel Target TargetSafe Driver LB_Logic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store cho Target.ops lib_free_opt].

Definition SJ_CALL_TOTAL : Z := 920000000.

Definition TGT_TOTAL : Z := 1060000000.

Definition PARSER_MAX : Z := 14340000.
Lemma atp_parser_total : forall L, 0 <= L <= SJ_PADMAX ->
  0 <= SJ_SBUF L /\ 0 <= SJ_TAPE L /\ 0 <= SJ_IDX L /\
  SJ_SBUF L + SJ_TAPE L + SJ_IMPL + SJ_IDX L + SJ_OC + SJ_IA <= PARSER_MAX.
Proof.
  intros L H. unfold SJ_SBUF, SJ_TAPE, SJ_IDX, SJ_IMPL, SJ_OC, SJ_IA, SJ_PADMAX, PARSER_MAX, sj_cap in *.
  pose proof (roundup64_ge (5 * (Z.max L 32 / 3) + 64)). pose proof (roundup64_lt (5 * (Z.max L 32 / 3) + 64)).
  pose proof (roundup64_ge (Z.max L 32 + 3)). pose proof (roundup64_lt (Z.max L 32 + 3)).
  pose proof (roundup64_ge (Z.max L 32)). pose proof (roundup64_lt (Z.max L 32)).
  assert (0 <= Z.max L 32 / 3 <= 349504) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  lia.
Qed.

Lemma atp_budget : 2 * (MAX_INPUT + 1) + (12 * MAX_INPUT + 64) <= TGT_TOTAL
  /\ 2 * (MAX_INPUT + 1) + (8 * MAX_INPUT + 64) + (MAX_INPUT + 64) + PARSER_MAX + (SJ_PADMAX + 64) + (MAX_INPUT + 8) <= TGT_TOTAL.
Proof. unfold MAX_INPUT, TGT_TOTAL, SJ_PADMAX, PARSER_MAX. lia. Qed.

Section TargetL.
Context {St ptr : Type}.
Variable B : Z.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.
Variable own : list (ptr * Z) -> assn St.
Variable mal_ok : list (ptr * Z) -> Z -> Prop.

Hypothesis Hdm : forall X n, 0 <= n ->
  mspecL B (fun s mo => own X s mo /\ mal_ok X n) (raw_malloc n)
         (fun r s mo => match r with Some p => own ((p, n) :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p n, mspecL B (own ((p, n) :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hout : forall X ps, mspecL B (own X) (stdout_vprintf get_so set_so ps) (fun _ => own X).

Fixpoint sumX (X : list (ptr * Z)) : Z := match X with [] => 0 | xb :: X' => snd xb + sumX X' end.
Definition nonnegX (X : list (ptr * Z)) : Prop := Forall (fun xb => 0 <= snd xb) X.
Hypothesis OK_tgt : forall X n, (length X <= 12)%nat -> nonnegX X -> 0 <= n -> sumX X + n <= TGT_TOTAL -> mal_ok X n.

Definition smallX (X : list (ptr * Z)) : Prop :=
  Forall (fun xb => 0 <= snd xb <= MAX_INPUT + 1) X.
Lemma smallX_app Y X : smallX Y -> smallX X -> smallX (Y ++ X).
Proof. intros; unfold smallX in *; apply Forall_app; auto. Qed.
Lemma smallX_cons p n X : 0 <= n <= MAX_INPUT + 1 -> smallX X -> smallX ((p, n) :: X).
Proof. intros; unfold smallX in *; constructor; auto. Qed.
Lemma smallX_nil : smallX [].
Proof. constructor. Qed.
Lemma smallX_tail x X : smallX (x :: X) -> smallX X.
Proof. intros H. inversion H. assumption. Qed.

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.

Lemma nonnegX_cons p n X : 0 <= n -> nonnegX X -> nonnegX ((p, n) :: X).
Proof. intros; unfold nonnegX in *; constructor; auto. Qed.

Lemma mspecL_ret_ops {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecL B P (ret ops a) Q.
Proof. intros H. cbn. apply mspecL_ret. exact H. Qed.
Lemma mspecL_bind_ops {A C} (m : Monad.M St A) (f : A -> Monad.M St C) P Q1 Q :
  mspecL B P m Q1 -> (forall a, mspecL B (Q1 a) (f a) Q) -> mspecL B P (bind ops m f) Q.
Proof. intros H1 H2. cbn. eapply mspecL_bind; eauto. Qed.

Lemma zlength_nonneg {A} (l : list A) : 0 <= zlength l.
Proof. unfold zlength. lia. Qed.

Lemma newnt_L : forall X n, (length X <= 12)%nat -> nonnegX X -> 0 <= n -> sumX X + n <= TGT_TOTAL ->
  mspecL B (own X) (newnt ops n) (fun p s mo => own ((p, n) :: X) s mo).
Proof.
  intros X n HL HX Hn Hs. unfold newnt.
  apply (mspecL_bind_ops _ _ _ (fun r s mo => match r with Some p => own ((p, n) :: X) s mo | None => True end)).
  { red_ops. eapply mspecL_conseq; [apply (Hdm X n Hn)| |].
    - intros s mo H. split; [exact H|]. apply OK_tgt; assumption.
    - intros [p|] s mo H; [exact (proj1 H)| exact I]. }
  intros [p|]; [apply mspecL_ret_ops; auto| red_ops; apply mspecL_munr].
Qed.

Lemma del_L : forall X Y p n, Permutation Y ((p, n) :: X) -> mspecL B (own Y) (del ops p) (fun _ => own X).
Proof.
  intros X Y p n HP. unfold del. red_ops. eapply mspecL_pre; [apply (Hdf X p n)|].
  intros s mo H. exact (Hperm _ _ s mo HP H).
Qed.

Lemma mspecL_chok_ops {C} (k : Z -> Monad.M St C) P Q :
  (forall z, mspecL B P (k z) Q) -> mspecL B P (bind ops (cho ops) k) Q.
Proof. intros H. cbn. apply mspecL_chok. exact H. Qed.

Lemma sumX_app : forall Y X, sumX (Y ++ X) = sumX Y + sumX X.
Proof. induction Y as [|[p n] Y IH]; intros X; cbn; [lia|]. rewrite IH. lia. Qed.
Lemma nonnegX_app : forall Y X, nonnegX Y -> nonnegX X -> nonnegX (Y ++ X).
Proof. intros; unfold nonnegX in *; apply Forall_app; auto. Qed.

Section Calls.
Variable X : list (ptr * Z).
Hypothesis HX : (length X <= 2)%nat.
Hypothesis NX : nonnegX X.
Hypothesis SX : sumX X <= 2 * (MAX_INPUT + 1).
Variable d : list Z.
Hypothesis Hd : zlength d <= MAX_INPUT.

Lemma sj_call_total : forall len rc, 0 <= len <= MAX_INPUT -> rc_ok len rc ->
  0 <= SJ_SBUF len /\ 0 <= SJ_TAPE len /\ 0 <= SJ_IDX len /\ 0 <= SJ_COPY len /\ 0 <= match rc with Some c => c | None => 0 end
  /\ SJ_SBUF len + SJ_TAPE len + SJ_IMPL + SJ_IDX len + SJ_OC + SJ_IA
     + (if len <=? SJ_PADMAX then SJ_COPY len + match rc with Some c => c | None => 0 end else 0) <= SJ_CALL_TOTAL.
Proof.
  intros len rc H Hrc. unfold SJ_SBUF, SJ_TAPE, SJ_IDX, SJ_COPY, SJ_IMPL, SJ_OC, SJ_IA, SJ_PADMAX, SJ_CALL_TOTAL, sj_cap, MAX_INPUT in *.
  pose proof (roundup64_ge (5 * (Z.max len 32 / 3) + 64)). pose proof (roundup64_lt (5 * (Z.max len 32 / 3) + 64)).
  pose proof (roundup64_ge (Z.max len 32 + 3)). pose proof (roundup64_lt (Z.max len 32 + 3)).
  pose proof (roundup64_ge (Z.max len 32)). pose proof (roundup64_lt (Z.max len 32)).
  assert (0 <= Z.max len 32 / 3 <= 22369622) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  destruct (Z.leb_spec len 1048512); destruct rc as [c|]; cbn in Hrc; lia.
Qed.

Definition oX (b : option ptr) (c : Z) : list (ptr * Z) := match b with Some p => [(p, c)] | None => [] end.
Definition CHAIN_PEAK : Z := 201326592.

Lemma del_opt_L : forall Y b c, mspecL B (own (oX b c ++ Y)) (del_opt ops b) (fun _ => own Y).
Proof.
  intros Y [p|] c; unfold del_opt; cbn [oX app].
  - eapply del_L. apply Permutation_refl.
  - apply mspecL_ret_ops. intros s mo H. exact H.
Qed.

Lemma pj_chain_L : forall fuel len cap b Y, 0 <= len <= SJ_PADMAX -> IMP_SCAP0 <= cap -> cap <= 134217728 ->
  (length Y <= 11)%nat -> nonnegX Y -> sumX Y + CHAIN_PEAK <= TGT_TOTAL ->
  mspecL B (own (oX b cap ++ Y)) (pj_chain ops fuel len cap b)
         (fun b' s mo => exists c', own (oX b' c' ++ Y) s mo /\ 0 <= c' <= 134217728).
Proof.
  induction fuel as [|f IH]; intros len cap b Y Hl Hc Hc2 LY NY SY; cbn [pj_chain].
  - apply mspecL_ret_ops. intros s mo H. exists cap. split; [exact H| unfold IMP_SCAP0 in Hc; lia].
  - apply mspecL_chok_ops. intros z. destruct (chain_ok len cap z) eqn:E.
    + pose proof (schain_ok_step len cap z Hl Hc E) as (Hz0 & Hz1 & Hz2). unfold IMP_SCAP0, CHAIN_PEAK in *.
      apply (mspecL_bind_ops _ _ _ (fun p s mo => own ((p, z) :: oX b cap ++ Y) s mo)).
      { apply newnt_L.
        - destruct b; cbn [oX app length]; lia.
        - destruct b; cbn [oX app]; [apply nonnegX_cons; [lia| exact NY]| exact NY].
        - lia.
        - destruct b; cbn [oX app sumX snd]; lia. }
      intros p. apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((p, z) :: Y) s mo)).
      * destruct b as [b0|]; unfold del_opt; cbn [oX app].
        -- eapply del_L. apply perm_swap.
        -- apply mspecL_ret_ops. intros s mo H. exact H.
      * intros _. apply (IH len z (Some p) Y Hl); [lia| lia| exact LY| exact NY| exact SY].
    + apply mspecL_ret_ops. intros s mo H. exists cap. split; [exact H| unfold IMP_SCAP0 in Hc; lia].
Qed.

Lemma pj_free_nulls_L : forall Y, mspecL B (own Y) (pj_free_nulls ops) (fun _ => own Y).
Proof.
  intros Y. unfold pj_free_nulls.
  repeat (apply (mspecL_bind_ops _ _ _ (fun _ => own Y)); [red_ops; apply mspecL_ret; auto| intros _]).
  red_ops. apply mspecL_ret. auto.
Qed.

Definition IMP_PEAK : Z := 134217728 + CHAIN_PEAK.

Lemma imp_copy_L : forall len Y, 0 <= len <= SJ_PADMAX -> (length Y <= 12)%nat -> nonnegX Y -> sumX Y + 134217728 <= TGT_TOTAL ->
  mspecL B (own Y) (imp_copy ops len) (fun c s mo => exists c', own (oX c c' ++ Y) s mo).
Proof.
  intros len Y Hl LY NY SY. unfold imp_copy. apply mspecL_chok_ops. intros S. destruct (copy_ok len S) eqn:E.
  - apply copy_ok_spec in E. pose proof (PJ_CAPMAX_bound len Hl) as HB.
    apply (mspecL_bind_ops _ _ _ (fun b s mo => own ((b, S) :: Y) s mo)).
    + apply newnt_L; [exact LY| exact NY| lia| lia].
    + intros b. apply mspecL_ret_ops. intros s mo H. exists S. exact H.
  - apply mspecL_ret_ops. intros s mo H. exists 0. exact H.
Qed.

Lemma imp_print_L : forall len Y, 0 <= len <= SJ_PADMAX ->
  (length Y <= 10)%nat -> nonnegX Y -> sumX Y + IMP_PEAK <= TGT_TOTAL ->
  mspecL B (own Y) (imp_print ops len) (fun _ => own Y).
Proof.
  intros len Y Hl LY NY SY. unfold imp_print, IMP_PEAK, CHAIN_PEAK in *. apply mspecL_chok_ops. intros ok.
  destruct (ok =? 0); [apply mspecL_ret_ops; auto|].
  apply (mspecL_bind_ops _ _ _ (fun b s mo => exists c', own (oX b c' ++ Y) s mo /\ 0 <= c' <= 134217728)).
  { apply (pj_chain_L PJ_FUEL len PJ_INLINE None Y Hl); [unfold IMP_SCAP0, PJ_INLINE; lia| unfold PJ_INLINE; lia| lia| exact NY| unfold CHAIN_PEAK; lia]. }
  intros b. apply mspecL_exI. intros cb. apply mspecL_pure. intros Hcb.
  set (Y1 := oX b cb ++ Y).
  assert (LY1 : (length Y1 <= 11)%nat) by (subst Y1; destruct b; cbn [oX app length]; lia).
  assert (NY1 : nonnegX Y1) by (subst Y1; destruct b; cbn [oX app]; [apply nonnegX_cons; [lia| exact NY]| exact NY]).
  assert (SY1 : sumX Y1 <= sumX Y + 134217728) by (subst Y1; destruct b; cbn [oX app sumX snd]; lia).
  apply (mspecL_bind_ops _ _ _ (fun sb s mo => exists c', own (oX sb c' ++ Y1) s mo /\ 0 <= c' <= 134217728)).
  { apply (pj_chain_L PJ_FUEL len IMP_SCAP0 None Y1 Hl); [lia| unfold IMP_SCAP0; lia| exact LY1| exact NY1| unfold CHAIN_PEAK; lia]. }
  intros sb. apply mspecL_exI. intros cs. apply mspecL_pure. intros Hcs.

  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own (oX sb cs ++ Y) s mo)).
  { subst Y1. destruct b as [bp|]; unfold del_opt; cbn [oX app].
    - eapply del_L. destruct sb; cbn [oX app]; [apply perm_swap| apply Permutation_refl].
    - apply mspecL_ret_ops. intros s mo H. exact H. }
  intros _.

  apply (mspecL_bind_ops _ _ _ (fun c s mo => exists c', own (oX c c' ++ (oX sb cs ++ Y)) s mo)).
  { apply imp_copy_L; [exact Hl| destruct sb; cbn [oX app length]; lia| destruct sb; cbn [oX app]; [apply nonnegX_cons; [lia| exact NY]| exact NY]| destruct sb; cbn [oX app sumX snd]; lia]. }
  intros c. apply mspecL_exI. intros cc.

  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own (oX c cc ++ Y) s mo)).
  { destruct sb as [sp'|]; unfold del_opt; cbn [oX app].
    - eapply del_L. destruct c; cbn [oX app]; [apply perm_swap| apply Permutation_refl].
    - apply mspecL_ret_ops. intros s mo H. exact H. }
  intros _.
  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own (oX c cc ++ Y) s mo)); [apply pj_free_nulls_L|]. intros _.

  destruct c as [cp'|]; unfold del_opt; cbn [oX app].
  - eapply del_L. apply Permutation_refl.
  - apply mspecL_ret_ops. intros s mo H. exact H.
Qed.

Lemma pj_budget : 2 * (MAX_INPUT + 1) + IMP_VEC + PARSER_MAX + (SJ_PADMAX + 64) + IMP_PEAK <= TGT_TOTAL.
Proof. unfold MAX_INPUT, TGT_TOTAL, SJ_PADMAX, PARSER_MAX, IMP_PEAK, CHAIN_PEAK, IMP_VEC. lia. Qed.

Lemma imp_static_L : forall v,
  mspecL B (own (oX v IMP_VEC ++ X)) (imp_static ops v) (fun v' s mo => exists p, own ((p, IMP_VEC) :: X) s mo /\ v' = Some p).
Proof.
  intros [p|]; unfold imp_static; cbn [oX app].
  - apply mspecL_ret_ops. intros s mo H. exists p. split; [exact H| reflexivity].
  - apply (mspecL_bind_ops _ _ _ (fun p s mo => own ((p, IMP_VEC) :: X) s mo)).
    + apply newnt_L; [lia| exact NX| unfold IMP_VEC; lia| unfold IMP_VEC, TGT_TOTAL, MAX_INPUT in *; lia].
    + intros p. apply mspecL_ret_ops. intros s mo H. exists p. split; [exact H| reflexivity].
Qed.

Lemma fuzz_one_with_L : forall rc v, rc_ok (zlength d) rc ->
  mspecL B (own (oX v IMP_VEC ++ X)) (fuzz_one_with ops d rc v)
         (fun r => fun s mo => exists p, own ((p, IMP_VEC) :: X) s mo /\ (snd r = Some p /\ fst r = 0)).
Proof.
  intros rc v Hrc. unfold fuzz_one_with, imp_copy_phase. pose proof (zlength_nonneg d) as Hd0.
  apply (mspecL_bind_ops _ _ _ (fun v' s mo => exists p, own ((p, IMP_VEC) :: X) s mo /\ v' = Some p)); [apply imp_static_L|]. intros v'.
  apply mspecL_exI. intros p. apply mspecL_pure. intros ->. unfold IMP_VEC in *.
  pose proof (sj_call_total (zlength d) rc (conj Hd0 Hd) Hrc) as (HS & HT & HI & HC & HR & HTOT).
  pose proof pj_budget as HPB.
  assert (HPAR : zlength d <= SJ_PADMAX -> SJ_SBUF (zlength d) + SJ_TAPE (zlength d) + SJ_IMPL + SJ_IDX (zlength d) + SJ_OC + SJ_IA <= PARSER_MAX).
  { intros Hle. exact (proj2 (proj2 (proj2 (atp_parser_total (zlength d) (conj Hd0 Hle))))). }
  set (len := zlength d) in *. set (S := SJ_SBUF len) in *. set (T := SJ_TAPE len) in *. set (I := SJ_IDX len) in *. set (C := SJ_COPY len) in *.
  set (rcv := match rc with Some c => c | None => 0 end) in *.
  assert (HZ : 0 <= (if len <=? SJ_PADMAX then C + rcv else 0)) by (destruct (len <=? SJ_PADMAX); lia).
  set (Z0 := if len <=? SJ_PADMAX then C + rcv else 0) in *.
  unfold SJ_CALL_TOTAL, TGT_TOTAL, SJ_IMPL, SJ_OC, SJ_IA, MAX_INPUT, PARSER_MAX, IMP_PEAK, CHAIN_PEAK in *.
  Ltac nn := repeat (apply nonnegX_cons; [lia|]); assumption.
  apply (mspecL_bind_ops _ _ _ (fun sb s mo => own ((sb, S) :: (p, 8) :: X) s mo)).
  { apply newnt_L; [cbn [length]; lia| nn| lia| cbn [sumX snd]; unfold TGT_TOTAL; lia]. } intros sb.
  apply (mspecL_bind_ops _ _ _ (fun tp s mo => own ((tp, T) :: (sb, S) :: (p, 8) :: X) s mo)).
  { apply newnt_L; [cbn [length]; lia| nn| lia| cbn [sumX snd]; unfold TGT_TOTAL; lia]. } intros tp.
  apply (mspecL_bind_ops _ _ _ (fun im s mo => own ((im, 96) :: (tp, T) :: (sb, S) :: (p, 8) :: X) s mo)).
  { apply newnt_L; [cbn [length]; lia| nn| lia| cbn [sumX snd]; unfold TGT_TOTAL; lia]. } intros im.
  apply (mspecL_bind_ops _ _ _ (fun ix s mo => own ((ix, I) :: (im, 96) :: (tp, T) :: (sb, S) :: (p, 8) :: X) s mo)).
  { apply newnt_L; [cbn [length]; lia| nn| lia| cbn [sumX snd]; unfold TGT_TOTAL; lia]. } intros ix.
  apply (mspecL_bind_ops _ _ _ (fun oc s mo => own ((oc, 8192) :: (ix, I) :: (im, 96) :: (tp, T) :: (sb, S) :: (p, 8) :: X) s mo)).
  { apply newnt_L; [cbn [length]; lia| nn| lia| cbn [sumX snd]; unfold TGT_TOTAL; lia]. } intros oc.
  apply (mspecL_bind_ops _ _ _ (fun ia s mo => own ((ia, 1024) :: (oc, 8192) :: (ix, I) :: (im, 96) :: (tp, T) :: (sb, S) :: (p, 8) :: X) s mo)).
  { apply newnt_L; [cbn [length]; lia| nn| lia| cbn [sumX snd]; unfold TGT_TOTAL; lia]. } intros ia.
  set (X6 := (ia, 1024) :: (oc, 8192) :: (ix, I) :: (im, 96) :: (tp, T) :: (sb, S) :: (p, 8) :: X).
  assert (L6 : (length X6 <= 9)%nat) by (unfold X6; cbn [length]; lia).
  assert (N6 : nonnegX X6) by (unfold X6; nn).
  assert (S6 : sumX X6 = 1024 + 8192 + I + 96 + T + S + (8 + sumX X)) by (unfold X6; cbn [sumX snd]; lia).
  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own X6 s mo)).
  { subst Z0. destruct (Z.leb_spec len SJ_PADMAX) as [Hle|Hgt]; [| apply mspecL_ret_ops; auto].
    specialize (HPAR Hle). unfold SJ_PADMAX in Hle.
    apply (mspecL_bind_ops _ _ _ (fun cp s mo => own ((cp, C) :: X6) s mo)).
    { apply newnt_L; [lia| exact N6| lia| rewrite S6; unfold TGT_TOTAL; lia]. } intros cp.
    apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((cp, C) :: X6) s mo)).
    { subst rcv. destruct rc as [c|]; [| apply mspecL_ret_ops; auto].
      apply (mspecL_bind_ops _ _ _ (fun r s mo => own ((r, c) :: (cp, C) :: X6) s mo)).
      + apply newnt_L; [cbn [length]; lia| apply nonnegX_cons; [lia| exact N6]| lia| cbn [sumX snd]; rewrite S6; unfold TGT_TOTAL; lia].
      + intros r. eapply del_L. apply Permutation_refl. }
    intros _.
    apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((cp, C) :: X6) s mo)).
    { apply imp_print_L; [unfold SJ_PADMAX; lia| cbn [length]; lia| apply nonnegX_cons; [lia| exact N6]|].
      cbn [sumX snd]. rewrite S6. subst C. unfold SJ_COPY, IMP_PEAK, CHAIN_PEAK, TGT_TOTAL, IMP_VEC in *. lia. }
    intros _. eapply del_L. apply Permutation_refl. } intros _.
  unfold X6.
  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((ia, 1024) :: (oc, 8192) :: (ix, I) :: (im, 96) :: (tp, T) :: (p, 8) :: X) s mo)).
  { eapply del_L. apply Permutation_sym. exact (Permutation_middle [(ia, 1024); (oc, 8192); (ix, I); (im, 96); (tp, T)] ((p, 8) :: X) (sb, S)). } intros _.
  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((ia, 1024) :: (oc, 8192) :: (ix, I) :: (im, 96) :: (p, 8) :: X) s mo)).
  { eapply del_L. apply Permutation_sym. exact (Permutation_middle [(ia, 1024); (oc, 8192); (ix, I); (im, 96)] ((p, 8) :: X) (tp, T)). } intros _.
  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((oc, 8192) :: (ix, I) :: (im, 96) :: (p, 8) :: X) s mo)); [eapply del_L; apply Permutation_refl|]. intros _.
  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((ix, I) :: (im, 96) :: (p, 8) :: X) s mo)); [eapply del_L; apply Permutation_refl|]. intros _.
  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((im, 96) :: (p, 8) :: X) s mo)); [eapply del_L; apply Permutation_refl|]. intros _.
  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((p, 8) :: X) s mo)); [eapply del_L; apply Permutation_refl|]. intros _.
  apply mspecL_ret_ops. intros s mo H. exists p. split; [exact H|]. split; reflexivity.
Qed.

Lemma fuzz_one_L : forall v,
  mspecL B (own (oX v IMP_VEC ++ X)) (fuzz_one ops d v)
         (fun r => fun s mo => exists p, own ((p, IMP_VEC) :: X) s mo /\ (snd r = Some p /\ fst r = 0)).
Proof. intros v. unfold fuzz_one. apply fuzz_one_with_L. apply sj_root_copy_ok. Qed.

Lemma run_calls_L : forall n rc v,
  rc = 0 ->
  mspecL B (own (oX v IMP_VEC ++ X)) (ImpModel.run_calls ops d n rc v)
         (fun r => fun s mo => own (oX (snd r) IMP_VEC ++ X) s mo /\ fst r = 0).
Proof.
  induction n as [|n IH]; intros rc v Hrc; cbn [ImpModel.run_calls].
  - apply mspecL_ret_ops. intros s mo H. cbn [fst snd]. auto.
  - apply (mspecL_bind_ops _ _ _ (fun r => fun s mo => exists p, own ((p, IMP_VEC) :: X) s mo /\ (snd r = Some p /\ fst r = 0))); [apply fuzz_one_L|].
    intros r. apply mspecL_exI. intros p. apply mspecL_pure. intros [Hr Hz]. apply (mspecL_bind_ops _ _ _ (fun _ => own ((p, IMP_VEC) :: X))).
    + red_ops. apply Hout.
    + intros u. rewrite Hr. apply (IH (fst r) (Some p)). exact Hz.
Qed.
End Calls.
End TargetL.

Theorem target_run_L {St ptr : Type} (B : Z)
  (raw_malloc : Z -> Monad.M St (option ptr)) (raw_free : ptr -> Monad.M St unit)
  (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St)
  (own : list (ptr * Z) -> assn St) (mal_ok : list (ptr * Z) -> Z -> Prop) :
  (forall X n, 0 <= n ->
     mspecL B (fun s mo => own X s mo /\ mal_ok X n) (raw_malloc n)
            (fun r s mo => match r with Some p => own ((p, n) :: X) s mo /\ n < 2^63 | None => own X s mo end)) ->
  (forall X p n, mspecL B (own ((p, n) :: X)) (raw_free p) (fun _ => own X)) ->
  (forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo) ->
  (forall X ps, mspecL B (own X) (stdout_vprintf get_so set_so ps) (fun _ => own X)) ->
  (forall X n, (length X <= 12)%nat -> nonnegX X -> 0 <= n -> sumX X + n <= TGT_TOTAL -> mal_ok X n) ->
  forall X0 cfg payload, (length X0 <= 1)%nat -> nonnegX X0 -> sumX X0 <= MAX_INPUT + 1 -> zlength payload <= MAX_INPUT ->
  mspecL B (own X0) (Target.target_run raw_malloc raw_free get_so set_so cfg payload) (fun r s mo => own (oX (snd r) IMP_VEC ++ X0) s mo).
Proof.
  intros Hdm Hdf Hperm Hout OK X0 cfg payload HX0 NX0 SX0 Hpl.
  unfold Target.target_run, ImpModel.target_run.
  pose proof (@zlength_nonneg Z payload) as Hpl0.
  apply (mspecL_bind _ _ _ _
           (fun a s mo => match a with
                          | None => own X0 s mo
                          | Some None => own X0 s mo
                          | Some (Some p) => own ((p, zlength payload) :: X0) s mo
                          end)).
  - destruct (zlength payload =? 0) eqn:EZ.
    + cbn. apply mspecL_ret. intros s mo H. exact H.
    + cbn -[MAX_INPUT].
      apply (mspecL_bind _ _ _ _
               (fun r s mo => match r with Some p => own ((p, zlength payload) :: X0) s mo | None => own X0 s mo end)).
      * eapply mspecL_conseq; [apply (Hdm X0 (zlength payload)); lia| |].
        -- intros s mo H. split; [exact H|]. apply OK; [lia| exact NX0| lia| unfold TGT_TOTAL, MAX_INPUT in *; lia].
        -- intros [p|] s mo H; [exact (proj1 H)| exact H].
      * intros [p|]; apply mspecL_ret; intros s mo H; exact H.
  - intros [[p|]|]; [| |cbn; apply mspecL_munr].
    + cbn -[MAX_INPUT ImpModel.run_calls].
      assert (HXX : (length ((p, zlength payload) :: X0) <= 2)%nat) by (cbn [length]; lia).
      assert (NXX : nonnegX ((p, zlength payload) :: X0)) by (apply nonnegX_cons; [lia| exact NX0]).
      assert (SXX : sumX ((p, zlength payload) :: X0) <= 2 * (MAX_INPUT + 1)) by (cbn [sumX snd]; lia).
      apply (mspecL_bind _ _ _ _ (fun r => fun s mo => own (oX (snd r) IMP_VEC ++ (p, zlength payload) :: X0) s mo /\ fst r = 0)).
      { apply (@run_calls_L St ptr B raw_malloc raw_free get_so set_so own mal_ok Hdm Hdf Hperm Hout OK _ HXX NXX SXX payload Hpl _ 0 None). reflexivity. }
      intros r. apply (mspecL_bind _ _ _ _ (fun _ s mo => own (oX (snd r) IMP_VEC ++ X0) s mo)).
      * eapply mspecL_pre; [apply Hdf|]. intros s mo [H _]. eapply Hperm; [| exact H]. destruct (snd r); cbn [oX app]; [apply perm_swap| apply Permutation_refl].
      * intros u. apply mspecL_ret. intros s mo H. exact H.
    + cbn -[MAX_INPUT ImpModel.run_calls].
      assert (HXX : (length X0 <= 2)%nat) by lia.
      assert (SXX : sumX X0 <= 2 * (MAX_INPUT + 1)) by (unfold MAX_INPUT in *; lia).
      apply (mspecL_bind _ _ _ _ (fun r => fun s mo => own (oX (snd r) IMP_VEC ++ X0) s mo /\ fst r = 0)).
      { apply (@run_calls_L St ptr B raw_malloc raw_free get_so set_so own mal_ok Hdm Hdf Hperm Hout OK _ HXX NX0 SXX payload Hpl _ 0 None). reflexivity. }
      intros r. apply (mspecL_bind _ _ _ _ (fun _ s mo => own (oX (snd r) IMP_VEC ++ X0) s mo)).
      * apply mspecL_ret. intros s mo H. exact (proj1 H).
      * intros u. apply mspecL_ret. intros s mo H. exact H.
Qed.
