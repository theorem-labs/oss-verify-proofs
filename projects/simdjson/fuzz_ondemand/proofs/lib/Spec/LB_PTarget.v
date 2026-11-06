(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim Monad MSafe Stdio SjModel AtpModel OdModel Target TargetSafe Driver LB_Logic.
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

Lemma od_parser_total : forall L, 0 <= L <= SJ_PADMAX ->
  0 <= OD_SBUF L /\ 0 <= OD_IDX L /\
  OD_SBUF L + SJ_IMPL + OD_IDX L + SJ_OC + SJ_IA <= PARSER_MAX.
Proof.
  intros L H. unfold OD_SBUF, OD_IDX, SJ_IMPL, SJ_OC, SJ_IA, SJ_PADMAX, PARSER_MAX in *.
  pose proof (roundup64_ge (5 * (L / 3) + 64)). pose proof (roundup64_lt (5 * (L / 3) + 64)).
  pose proof (roundup64_ge L). pose proof (roundup64_lt L).
  assert (0 <= L / 3 <= 349504) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
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
Hypothesis OK_tgt : forall X n, (length X <= 10)%nat -> nonnegX X -> 0 <= n -> sumX X + n <= TGT_TOTAL -> mal_ok X n.

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

Lemma newnt_L : forall X n, (length X <= 10)%nat -> nonnegX X -> 0 <= n -> sumX X + n <= TGT_TOTAL ->
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

Definition vX (v : vec (ptr:=ptr)) : list (ptr * Z) := match v with (cap, _, Some b) => [(b, VELT * cap)] | _ => [] end.
Let P : Z := Z.of_nat (od_P d).

Lemma P_bound : 4 * (P - 1) <= zlength d + 4 /\ 1 <= P.
Proof. subst P. pose proof (od_P_bound d). pose proof (od_P_ge1 d). unfold zlength. lia. Qed.

Lemma vpush_L : forall v, TargetSafe.vok v -> TargetSafe.vsize v + 1 <= P ->
  mspecL B (own (vX v ++ X)) (vpush ops v)
         (fun v' s mo => own (vX v' ++ X) s mo /\ TargetSafe.vok v' /\ TargetSafe.vsize v' = TargetSafe.vsize v + 1).
Proof.
  intros [[cap size] blk] [Hs Hc] HP. unfold vpush. cbn [TargetSafe.vsize vX] in *.
  pose proof P_bound as [HP4 HP2]. pose proof (proj1 atp_budget) as HB. unfold MAX_INPUT in *.
  destruct (Z.ltb_spec size cap) as [Hlt|Hge].
  - apply mspecL_ret_ops. intros s mo H. split; [exact H|]. unfold TargetSafe.vok. cbn. repeat split; lia.
  - unfold vcap_next. set (cap' := Z.max (2 * cap) (size + 1)).
    assert (Hcap' : 0 <= cap' <= 2 * size + 1) by (subst cap'; lia).
    apply (mspecL_bind_ops _ _ _ (fun b s mo => own ((b, VELT * cap') :: (match blk with Some b0 => [(b0, VELT * cap)] | None => [] end) ++ X) s mo)).
    { apply newnt_L.
      - destruct blk; cbn [length app]; lia.
      - destruct blk; [apply nonnegX_cons; [unfold VELT; lia| exact NX]| exact NX].
      - unfold VELT; lia.
      - destruct blk; cbn [sumX snd app]; unfold VELT, TGT_TOTAL in *; lia. }
    intros b. apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((b, VELT * cap') :: X) s mo)).
    + destruct blk as [b0|].
      * eapply del_L. apply perm_swap.
      * apply mspecL_ret_ops. intros s mo H. exact H.
    + intros _. apply mspecL_ret_ops. intros s mo H. split; [exact H|]. unfold TargetSafe.vok. cbn. repeat split; lia.
Qed.

Lemma vpushes_L : forall n v, TargetSafe.vok v -> TargetSafe.vsize v + Z.of_nat n <= P ->
  mspecL B (own (vX v ++ X)) (vpushes ops n v)
         (fun v' s mo => own (vX v' ++ X) s mo /\ TargetSafe.vok v' /\ TargetSafe.vsize v' = TargetSafe.vsize v + Z.of_nat n).
Proof.
  induction n as [|n IH]; intros v Hv Hb; cbn [vpushes].
  - apply mspecL_ret_ops. intros s mo H. repeat split; [exact H| exact Hv| lia].
  - apply (mspecL_bind_ops _ _ _ (fun v' s mo => own (vX v' ++ X) s mo /\ TargetSafe.vok v' /\ TargetSafe.vsize v' = TargetSafe.vsize v + 1)).
    { apply vpush_L; [exact Hv| lia]. }
    intros v'. apply mspecL_pointwise. intros s0 mo0 (H0 & Hv' & Hs').
    eapply mspecL_conseq; [apply (IH v' Hv'); lia| |].
    + intros s mo [-> ->]. exact H0.
    + intros v'' s mo (H & Hv'' & Hs''). repeat split; [exact H| exact Hv''| lia].
Qed.

Lemma vX_bound : forall v, TargetSafe.vok v -> TargetSafe.vsize v <= P ->
  (length (vX v) <= 1)%nat /\ nonnegX (vX v) /\ sumX (vX v) <= 8 * MAX_INPUT + 64.
Proof.
  intros [[cap size] [b|]] [Hs Hc] HP; cbn [vX TargetSafe.vsize length sumX snd] in *.
  - pose proof P_bound as [HP4 _]. unfold MAX_INPUT in *. split; [lia|]. split; [apply nonnegX_cons; [unfold VELT; lia| constructor]|]. unfold VELT. lia.
  - split; [lia|]. split; [constructor| unfold MAX_INPUT; lia].
Qed.

Lemma vfree_L : forall v, mspecL B (own (vX v ++ X)) (vfree ops v) (fun _ => own X).
Proof.
  intros [[cap size] [b|]]; unfold vfree; cbn [vX app].
  - eapply del_L. apply Permutation_refl.
  - apply mspecL_ret_ops. intros s mo H. exact H.
Qed.

Lemma atp_walk_L : forall segs Y, (length Y <= 9)%nat -> nonnegX Y -> sumX Y + (MAX_INPUT + 8) <= TGT_TOTAL ->
  (forall k, In k segs -> zlength k <= zlength d) ->
  mspecL B (own Y) (atp_walk ops segs) (fun _ => own Y).
Proof.
  induction segs as [|k rest IH]; intros Y HL NY SY Hlen; cbn [atp_walk].
  - apply mspecL_ret_ops. auto.
  - apply mspecL_chok_ops. intros z.
    destruct (z =? 0); [apply mspecL_ret_ops; auto|].
    apply (mspecL_bind_ops _ _ _ (fun _ => own Y)).
    + destruct (seg_alloc z k); [| apply mspecL_ret_ops; auto].
      pose proof (TargetSafe.zlength_nonneg k) as Hk0. pose proof (str_sz_bound (zlength k) Hk0). specialize (Hlen k (or_introl eq_refl)).
      apply (mspecL_bind_ops _ _ _ (fun p s mo => own ((p, str_sz (zlength k)) :: Y) s mo)).
      * apply newnt_L; [lia| exact NY| lia| unfold MAX_INPUT in *; lia].
      * intros p. eapply del_L. apply Permutation_refl.
    + intros _. apply IH; [exact HL| exact NY| exact SY|]. intros k' Hk'. apply Hlen. right. exact Hk'.
Qed.

Lemma fuzz_one_L :
  mspecL B (own X) (OdModel.fuzz_one ops d) (fun r => fun s mo => own X s mo /\ r = 0).
Proof.
  unfold OdModel.fuzz_one. pose proof (zlength_nonneg d) as Hd0.
  pose proof (od_doc_len d) as (HL0 & HLS & HL & HLP). pose proof (od_s0_len d) as HS0.
  pose proof (zlength_nonneg (od_s0 d)) as HS00.
  set (L := zlength (od_doc d)) in *. set (len0 := zlength (od_s0 d)) in *.
  pose proof (od_parser_total L (conj HL0 HLP)) as (HS & HI & HTOT).
  set (S := OD_SBUF L) in *. set (I := OD_IDX L) in *.
  pose proof atp_budget as [_ HB]. pose proof P_bound as [HP4 HP2].
  unfold SJ_IMPL, SJ_OC, SJ_IA in HTOT.
  Ltac nn := repeat (apply nonnegX_cons; [lia|]); try assumption.
  Ltac bl := unfold TGT_TOTAL, MAX_INPUT, SJ_PADMAX, PARSER_MAX, SJ_COPY, VELT in *; lia.

  apply (mspecL_bind_ops _ _ _ (fun v s mo => own (vX v ++ X) s mo /\ TargetSafe.vok v /\ TargetSafe.vsize v = TargetSafe.vsize (vec0 (ptr:=ptr)) + Z.of_nat (od_P d))).
  { apply (vpushes_L (od_P d) vec0); [cbn; lia| cbn [TargetSafe.vsize vec0]; subst P; lia]. }
  intros v. apply mspecL_pointwise. intros s0 mo0 (Hv0 & Hvok & Hvs). cbn [TargetSafe.vsize vec0] in Hvs.
  destruct (vX_bound v Hvok ltac:(subst P; lia)) as (VL & VN & VS). set (V := vX v) in *.
  eapply mspecL_pre; [| intros s mo [-> ->]; exact Hv0].
  assert (LVX : (length (V ++ X) <= 3)%nat) by (rewrite length_app; lia).
  assert (NVX : nonnegX (V ++ X)) by (apply nonnegX_app; assumption).
  pose proof (sumX_app V X) as SVX.
  unfold MAX_INPUT, TGT_TOTAL, SJ_PADMAX, PARSER_MAX in *.

  apply (mspecL_bind_ops _ _ _ (fun cpo s mo => own (match cpo with Some p => [(p, SJ_COPY len0)] | None => [] end ++ V ++ X) s mo)).
  { destruct (Z.leb_spec len0 1048512) as [Hle|Hgt].
    - apply (mspecL_bind_ops _ _ _ (fun p s mo => own ((p, SJ_COPY len0) :: V ++ X) s mo)).
      { apply newnt_L; [lia| exact NVX| bl| rewrite SVX; bl]. }
      intros p. apply mspecL_ret_ops. intros s mo H. exact H.
    - apply mspecL_ret_ops. intros s mo H. exact H. }
  intros cpo. set (C := match cpo with Some p => [(p, SJ_COPY len0)] | None => [] end).
  assert (LC : (length (C ++ V ++ X) <= 4)%nat) by (subst C; destruct cpo; cbn [length app]; rewrite ?length_app in *; cbn [length] in *; lia).
  assert (NC : nonnegX (C ++ V ++ X)) by (subst C; destruct cpo; [apply nonnegX_cons; [unfold SJ_COPY; lia| exact NVX]| exact NVX]).
  assert (SC : sumX (C ++ V ++ X) <= (67108864 + 64) + sumX V + sumX X).
  { subst C. destruct cpo; cbn [sumX app snd]; rewrite ?SVX; unfold SJ_COPY; lia. }

  apply (mspecL_bind_ops _ _ _ (fun sb s mo => own ((sb, S) :: C ++ V ++ X) s mo)).
  { apply newnt_L; [lia| exact NC| lia| bl]. } intros sb.
  apply (mspecL_bind_ops _ _ _ (fun im s mo => own ((im, 96) :: (sb, S) :: C ++ V ++ X) s mo)).
  { apply newnt_L; [cbn [length]; lia| nn| lia| cbn [sumX snd]; bl]. } intros im.
  apply (mspecL_bind_ops _ _ _ (fun ix s mo => own ((ix, I) :: (im, 96) :: (sb, S) :: C ++ V ++ X) s mo)).
  { apply newnt_L; [cbn [length]; lia| nn| lia| cbn [sumX snd]; bl]. } intros ix.
  apply (mspecL_bind_ops _ _ _ (fun oc s mo => own ((oc, 8192) :: (ix, I) :: (im, 96) :: (sb, S) :: C ++ V ++ X) s mo)).
  { apply newnt_L; [cbn [length]; lia| nn| lia| cbn [sumX snd]; bl]. } intros oc.
  apply (mspecL_bind_ops _ _ _ (fun ia s mo => own ((ia, 1024) :: (oc, 8192) :: (ix, I) :: (im, 96) :: (sb, S) :: C ++ V ++ X) s mo)).
  { apply newnt_L; [cbn [length]; lia| nn| lia| cbn [sumX snd]; bl]. } intros ia.
  set (X5 := [(ia, 1024); (oc, 8192); (ix, I); (im, 96); (sb, S)]).
  change ((ia, 1024) :: (oc, 8192) :: (ix, I) :: (im, 96) :: (sb, S) :: C ++ V ++ X) with (X5 ++ C ++ V ++ X).

  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own (X5 ++ V ++ X) s mo)).
  { subst C. destruct cpo as [p|].
    - eapply del_L. apply Permutation_sym. apply (Permutation_middle X5 (V ++ X)).
    - apply mspecL_ret_ops. intros s mo H. exact H. }
  intros _.

  subst X5. cbn [app].
  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((ia, 1024) :: (oc, 8192) :: (ix, I) :: (im, 96) :: V ++ X) s mo)).
  { eapply del_L. apply Permutation_sym. exact (Permutation_middle [(ia, 1024); (oc, 8192); (ix, I); (im, 96)] (V ++ X) (sb, S)). } intros _.
  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((oc, 8192) :: (ix, I) :: (im, 96) :: V ++ X) s mo)); [eapply del_L; apply Permutation_refl|]. intros _.
  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((ix, I) :: (im, 96) :: V ++ X) s mo)); [eapply del_L; apply Permutation_refl|]. intros _.
  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own ((im, 96) :: V ++ X) s mo)); [eapply del_L; apply Permutation_refl|]. intros _.
  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own (V ++ X) s mo)); [eapply del_L; apply Permutation_refl|]. intros _.

  apply (mspecL_bind_ops _ _ _ (fun _ s mo => own X s mo)); [subst V; apply vfree_L|]. intros _.
  apply mspecL_ret_ops. intros s mo H. auto.
Qed.

Lemma run_calls_L : forall n rc,
  rc = 0 ->
  mspecL B (own X) (OdModel.run_calls ops d n rc) (fun rc' => fun s mo => own X s mo /\ rc' = 0).
Proof.
  induction n as [|n IH]; intros rc Hrc; cbn [OdModel.run_calls].
  - apply mspecL_ret_ops. intros s mo H. auto.
  - apply (mspecL_bind_ops _ _ _ (fun rc' => fun s mo => own X s mo /\ rc' = 0)); [apply fuzz_one_L|].
    intros rc'. apply mspecL_pure. intros ->. apply (mspecL_bind_ops _ _ _ (fun _ => own X)).
    + red_ops. apply Hout.
    + intros u. apply IH. reflexivity.
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
  (forall X n, (length X <= 10)%nat -> nonnegX X -> 0 <= n -> sumX X + n <= TGT_TOTAL -> mal_ok X n) ->
  forall X0 cfg payload, (length X0 <= 1)%nat -> nonnegX X0 -> sumX X0 <= MAX_INPUT + 1 -> zlength payload <= MAX_INPUT ->
  mspecL B (own X0) (Target.target_run raw_malloc raw_free get_so set_so cfg payload) (fun _ => own X0).
Proof.
  intros Hdm Hdf Hperm Hout OK X0 cfg payload HX0 NX0 SX0 Hpl.
  unfold Target.target_run, OdModel.target_run.
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
  - intros [[p|]|]; [| |cbn; apply mspecL_ret; intros s mo H; exact H].
    + cbn -[MAX_INPUT OdModel.run_calls].
      assert (HXX : (length ((p, zlength payload) :: X0) <= 2)%nat) by (cbn [length]; lia).
      assert (NXX : nonnegX ((p, zlength payload) :: X0)) by (apply nonnegX_cons; [lia| exact NX0]).
      assert (SXX : sumX ((p, zlength payload) :: X0) <= 2 * (MAX_INPUT + 1)) by (cbn [sumX snd]; lia).
      apply (mspecL_bind _ _ _ _ (fun rc => fun s mo => own ((p, zlength payload) :: X0) s mo /\ rc = 0)).
      { apply (@run_calls_L St ptr B raw_malloc raw_free get_so set_so own mal_ok Hdm Hdf Hperm Hout OK _ HXX NXX SXX payload Hpl). reflexivity. }
      intros rc. apply (mspecL_bind _ _ _ _ (fun _ => own X0)).
      * eapply mspecL_pre; [apply Hdf|]. intros s mo H. exact (proj1 H).
      * intros u. apply mspecL_ret. intros s mo H. exact H.
    + cbn -[MAX_INPUT OdModel.run_calls].
      assert (HXX : (length X0 <= 2)%nat) by lia.
      assert (SXX : sumX X0 <= 2 * (MAX_INPUT + 1)) by (unfold MAX_INPUT in *; lia).
      apply (mspecL_bind _ _ _ _ (fun rc => fun s mo => own X0 s mo /\ rc = 0)).
      { apply (@run_calls_L St ptr B raw_malloc raw_free get_so set_so own mal_ok Hdm Hdf Hperm Hout OK _ HXX NX0 SXX payload Hpl). reflexivity. }
      intros rc. apply (mspecL_bind _ _ _ _ (fun _ => own X0)).
      * apply mspecL_ret. intros s mo H. exact (proj1 H).
      * intros u. apply mspecL_ret. intros s mo H. exact H.
Qed.
