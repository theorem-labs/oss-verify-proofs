(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzLemmasT BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCPermF BzCPermF2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCPermM BzCQsortM1 BzCQsortM2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC BzCSewD BzCSewE BzCSewF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA.BzCBudget OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewG.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zbok_mswap : forall a x y, zbok a -> zbok (mswap a x y).
Proof. intros. unfold mswap. apply zbok_wr32, zbok_wr32. assumption. Qed.
Lemma zbok_mvswap : forall f a p1 p2 n, zbok a -> zbok (mvswap f a p1 p2 n).
Proof. induction f; intros; cbn [mvswap]; [assumption|]. destruct (0 <? n); [apply IHf, zbok_mswap|]; assumption. Qed.
Lemma zbok_mpart_lo : forall f a2 d med p, zbok (mp_a1 p) -> zbok (mp_a1 (mpart_lo f a2 d med p)).
Proof.
  induction f; intros a2 d med p H; [exact H|]. rewrite mpart_lo_S. cbv zeta.
  destruct (mp_unHi p <? mp_unLo p); [exact H|]. destruct (_ =? 0); [apply IHf; cbn; apply zbok_mswap; exact H|].
  destruct (0 <? _); [exact H| apply IHf; cbn; exact H].
Qed.
Lemma zbok_mpart_hi : forall f a2 d med p, zbok (mp_a1 p) -> zbok (mp_a1 (mpart_hi f a2 d med p)).
Proof.
  induction f; intros a2 d med p H; [exact H|]. rewrite mpart_hi_S. cbv zeta.
  destruct (mp_unHi p <? mp_unLo p); [exact H|]. destruct (_ =? 0); [apply IHf; cbn; apply zbok_mswap; exact H|].
  destruct (_ <? 0); [exact H| apply IHf; cbn; exact H].
Qed.
Lemma zbok_mpart_loop : forall f sz a2 d med p, zbok (mp_a1 p) -> zbok (mp_a1 (mpart_loop f sz a2 d med p)).
Proof.
  induction f; intros sz a2 d med p H; [exact H|]. rewrite mpart_loop_S. cbv zeta.
  pose proof (zbok_mpart_hi (S sz) a2 d med _ (zbok_mpart_lo (S sz) a2 d med p H)) as H2.
  destruct (mp_unHi _ <? mp_unLo _); [exact H2|]. apply IHf. cbn. apply zbok_mswap. exact H2.
Qed.
Lemma zbok_mss_shift : forall f a1 a2 qoff nb d h lo j v b, zbok a1 -> zbok (fst (fst (mss_shift f a1 a2 qoff nb d h lo j v b))).
Proof.
  induction f; intros; [cbn; assumption|]. rewrite mss_shift_S. destruct (mainGtU _ _ _ _ _ _) as [gt b']. destruct gt; [| cbn; assumption].
  cbv zeta. destruct (_ <=? _); [cbn; apply zbok_wr32; assumption| apply IHf; apply zbok_wr32; assumption].
Qed.
Lemma zbok_mss_ins : forall a1 a2 qoff nb d h lo i b, zbok a1 -> zbok (fst (mss_ins a1 a2 qoff nb d h lo i b)).
Proof.
  intros. unfold mss_ins. pose proof (zbok_mss_shift (S (Z.to_nat (i - lo))) a1 a2 qoff nb d h lo i (rd32 a1 i) b H).
  destruct (mss_shift _ _ _ _ _ _ _ _ _ _ _) as [[a j] b']. cbn [fst] in *. apply zbok_wr32. exact H0.
Qed.
Lemma zbok_mss_hloop : forall f a1 a2 qoff nb d h lo hi i b, zbok a1 -> zbok (fst (fst (mss_hloop f a1 a2 qoff nb d h lo hi i b))).
Proof.
  induction f; intros; cbn [mss_hloop]; [cbn; assumption|].
  destruct (hi <? i); [cbn; assumption|].
  pose proof (zbok_mss_ins a1 a2 qoff nb d h lo i b H) as H1. destruct (mss_ins a1 _ _ _ _ _ _ i b) as [a11 b1]. cbn [fst] in H1.
  destruct (hi <? i + 1); [cbn; assumption|].
  pose proof (zbok_mss_ins a11 a2 qoff nb d h lo (i + 1) b1 H1) as H2. destruct (mss_ins a11 _ _ _ _ _ _ (i + 1) b1) as [a12 b2]. cbn [fst] in H2.
  destruct (hi <? i + 1 + 1); [cbn; assumption|].
  pose proof (zbok_mss_ins a12 a2 qoff nb d h lo (i + 1 + 1) b2 H2) as H3. destruct (mss_ins a12 _ _ _ _ _ _ (i + 1 + 1) b2) as [a13 b3]. cbn [fst] in H3.
  destruct (b3 <? 0); [cbn; assumption| apply IHf; assumption].
Qed.
Lemma zbok_mss_hps : forall n a1 a2 qoff nb d lo hi hp b, zbok a1 -> zbok (fst (fst (mss_hps n a1 a2 qoff nb d lo hi hp b))).
Proof.
  induction n; intros; cbn [mss_hps]; [cbn; assumption|].
  pose proof (zbok_mss_hloop (S (Z.to_nat (hi - lo + 1))) a1 a2 qoff nb d (incs_at hp) lo hi (lo + incs_at hp) b H) as H1.
  destruct (mss_hloop _ _ _ _ _ _ _ _ _ _ _) as [[a' b'] ex]. cbn [fst] in H1. destruct ex; [cbn; assumption| apply IHn; assumption].
Qed.
Lemma zbok_mainSimpleSort : forall a1 a2 qoff nb lo hi d b, zbok a1 -> zbok (fst (mainSimpleSort a1 a2 qoff nb lo hi d b)).
Proof.
  intros. unfold mainSimpleSort. destruct (_ <? 2); [cbn; assumption|].
  pose proof (zbok_mss_hps (Z.to_nat (mss_hp 15 (hi - lo + 1) 0 - 1 + 1)) a1 a2 qoff nb d lo hi (mss_hp 15 (hi - lo + 1) 0 - 1) b H) as H1.
  destruct (mss_hps _ _ _ _ _ _ _ _ _ _) as [[a' b'] e]. cbn [fst] in *. exact H1.
Qed.
Lemma zbok_mqs_iter : forall a2 qoff nb q, zbok (mq_a1 q) -> zbok (mq_a1 (mqs_iter a2 qoff nb q)).
Proof.
  intros a2 qoff nb q H. rewrite mqs_iter_ITER. unfold ITER.
  destruct (_ || _).
  - unfold LEAF. pose proof (zbok_mainSimpleSort (mq_a1 q) a2 qoff nb (TOPlo q) (TOPhi q) (TOPd q) (mq_budget q) H).
    destruct (mainSimpleSort _ _ _ _ _ _ _ _) as [a b]. cbn [mq_a1 fst] in *. exact H0.
  - assert (HP : zbok (mp_a1 (PART a2 q))) by (unfold PART; apply zbok_mpart_loop; cbn; exact H).
    destruct (_ <? _); [cbn; exact HP|].
    unfold PUSH3, mpush; cbn [mq_a1]. cps_destruct (net_spec (Q2 q (PART a2 q))) as (_ & _ & _ & _ & _ & _ & EA & _). rewrite EA.
    unfold Q2; cbn [mq_a1]. unfold A1V. apply zbok_mvswap, zbok_mvswap. exact HP.
Qed.
Lemma zbok_mqs_loop : forall f a2 qoff nb q, zbok (mq_a1 q) -> zbok (mq_a1 (mqs_loop f a2 qoff nb q)).
Proof. induction f; intros; [exact H|]. rewrite mqs_loop_S. destruct (_ && _); [apply IHf, zbok_mqs_iter|]; assumption. Qed.
Lemma zbok_mainQSort3 : forall a1 a2 qoff nb lo hi d b l, zbok a1 -> zbok (fst (fst (mainQSort3 a1 a2 qoff nb lo hi d b l))).
Proof. intros. unfold mainQSort3. cbn [fst]. apply zbok_mqs_loop. cbn. assumption. Qed.

Lemma zbok_qwr : forall a qoff i v, zbok a -> zbok (qwr a qoff i v).
Proof. intros. unfold qwr. apply zbok_wr16. assumption. Qed.
Lemma zbok_radix1 : forall n a ft qoff i j, zbok a -> zbok (fst (fst (ms_radix1 n a ft qoff i j))).
Proof. induction n; intros; cbn [ms_radix1]; [cbn; assumption|]. apply IHn. apply zbok_qwr. assumption. Qed.
Lemma zbok_overshoot : forall n a qoff nb i, zbok a -> zbok (ms_overshoot n a qoff nb i).
Proof. induction n; intros; cbn [ms_overshoot]; [assumption|]. apply IHn. apply zbok_qwr, zbok_wr8. assumption. Qed.
Lemma zbok_radix2 : forall n a1 a ft i s, zbok a1 -> zbok (fst (fst (ms_radix2 n a1 a ft i s))).
Proof. induction n; intros; cbn [ms_radix2]; [cbn; assumption|]. apply IHn. apply zbok_wr32. assumption. Qed.
Lemma zbok_quad : forall n b a1 qoff nb bbStart shifts j, zbok b -> zbok (ms_quad n b a1 qoff nb bbStart shifts j).
Proof.
  induction n; intros; [assumption|]. rewrite ms_quad_S. cbv zeta. apply IHn.
  destruct (_ <? _); [apply zbok_qwr|]; apply zbok_qwr; assumption.
Qed.
Lemma zbok_copy_fwd : forall f a1 cs a2 bd nb ss j, zbok a1 -> zbok (fst (fst (ms_copy_fwd f a1 cs a2 bd nb ss j))).
Proof.
  induction f; intros; [cbn; assumption|]. rewrite ms_copy_fwd_S. destruct (_ <? _); [| cbn; assumption]. cbv zeta.
  destruct (_ =? 0); apply IHf; [apply zbok_wr32|]; assumption.
Qed.
Lemma zbok_copy_bwd : forall f a1 ce a2 bd nb ss j, zbok a1 -> zbok (fst (fst (ms_copy_bwd f a1 ce a2 bd nb ss j))).
Proof.
  induction f; intros; [cbn; assumption|]. rewrite ms_copy_bwd_S. destruct (_ <? _); [| cbn; assumption]. cbv zeta.
  destruct (_ =? 0); apply IHf; [apply zbok_wr32|]; assumption.
Qed.
Lemma zbok_step1 : forall n qoff nb ss j s, zbok (s_a1 s) -> zbok (s_a1 (ms_step1 n qoff nb ss j s)) /\ s_a2 (ms_step1 n qoff nb ss j s) = s_a2 s.
Proof.
  induction n; intros; [split; [assumption| reflexivity]|]. rewrite ms_step1_S.
  destruct (s_exit s); [split; [assumption| reflexivity]|].
  destruct (j =? ss); [apply IHn; assumption|]. cbv zeta.
  assert (USE : forall s2, zbok (s_a1 s2) -> s_a2 s2 = s_a2 s -> zbok (s_a1 (ms_step1 n qoff nb ss (j + 1) s2)) /\ s_a2 (ms_step1 n qoff nb ss (j + 1) s2) = s_a2 s).
  { intros s2 Z2 E2. destruct (IHn qoff nb ss (j + 1) s2 Z2) as [A B]. split; [exact A| rewrite B; exact E2]. }
  destruct (negb _).
  - destruct (_ <? _).
    + pose proof (zbok_mainQSort3 (s_a1 s) (s_a2 s) qoff nb (clearmask (zget (s_ft s) (Z.shiftl ss 8 + j))) (clearmask (zget (s_ft s) (Z.shiftl ss 8 + j + 1)) - 1) BZ_N_RADIX (s_budget s) (s_mql s) H) as HQ.
      destruct (mainQSort3 _ _ _ _ _ _ _ _ _) as [[a1 b] l]. cbn [fst] in HQ.
      destruct (b <? 0); [cbn; split; [exact HQ| reflexivity]|].
      apply USE; [cbn; exact HQ| reflexivity].
    + apply USE; [cbn; assumption| reflexivity].
  - apply USE; [cbn; assumption| reflexivity].
Qed.
Lemma zbok_big : forall ro qoff nb i s, zbok (s_a1 s) -> zbok (s_a2 s) -> zbok (s_a1 (ms_big ro qoff nb i s)) /\ zbok (s_a2 (ms_big ro qoff nb i s)).
Proof.
  intros ro qoff nb i s H1 H2. unfold ms_big. cbv zeta.
  destruct (zbok_step1 256 qoff nb (zget ro i) 0 s H1) as [A1 A2].
  destruct (s_exit _); [rewrite A2; split; assumption|].
  destruct (ms_copy_init _ _ _ _ _ _) as [cs ce].
  match goal with |- context [ms_copy_fwd ?f ?a ?c ?b ?d ?n ?x ?j] => pose proof (zbok_copy_fwd f a c b d n x j A1) as F1; destruct (ms_copy_fwd f a c b d n x j) as [[af csf] jf] end.
  cbn [fst] in F1.
  match goal with |- context [ms_copy_bwd ?f ?a ?c ?b ?d ?n ?x ?j] => pose proof (zbok_copy_bwd f a c b d n x j F1) as F2; destruct (ms_copy_bwd f a c b d n x j) as [[ab ceb] jb] end.
  cbn [fst s_a1 s_a2] in *. split; [exact F2|]. rewrite A2. destruct (i <? 255); [apply zbok_quad|]; rewrite ?A2; assumption.
Qed.
Lemma zbok_bigs : forall n ro qoff nb i s, zbok (s_a1 s) -> zbok (s_a2 s) -> zbok (s_a1 (ms_bigs n ro qoff nb i s)) /\ zbok (s_a2 (ms_bigs n ro qoff nb i s)).
Proof.
  induction n; intros; [split; assumption|]. rewrite ms_bigs_S. cbv zeta. destruct (zbok_big ro qoff nb i s H H0) as [A B].
  destruct (s_exit _); [split; assumption| apply IHn; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma step1_exit : forall n qoff nb ss j s, (s_exit s = true -> s_budget s < 0) ->
  s_exit (ms_step1 n qoff nb ss j s) = true -> s_budget (ms_step1 n qoff nb ss j s) < 0.
Proof.
  induction n; intros qoff nb ss j s H; [exact H|]. rewrite ms_step1_S.
  destruct (s_exit s) eqn:E; [intros _; apply H; reflexivity|]. destruct (j =? ss); [apply IHn; rewrite E; intros; discriminate|]. cbv zeta.
  destruct (negb _).
  - destruct (_ <? _).
    + destruct (mainQSort3 _ _ _ _ _ _ _ _ _) as [[a1 b] l]. destruct (Z.ltb_spec b 0) as [L|L]; [cbn; intros; exact L|]. apply IHn. cbn. intros; discriminate.
    + apply IHn. cbn. intros; discriminate.
  - apply IHn. cbn. intros; discriminate.
Qed.
Lemma big_exit : forall ro qoff nb i s, s_exit s = false -> s_exit (ms_big ro qoff nb i s) = true -> s_budget (ms_big ro qoff nb i s) < 0.
Proof.
  intros ro qoff nb i s E. unfold ms_big.
  pose proof (step1_exit 256 qoff nb (zget ro i) 0 s ltac:(rewrite E; intros; discriminate)) as X.
  set (s1 := ms_step1 256 qoff nb (zget ro i) 0 s) in *. cbv zeta.
  destruct (s_exit s1) eqn:E1; [intros _; apply X; reflexivity|].
  destruct (ms_copy_init _ _ _ _ _ _) as [cs ce]. destruct (ms_copy_fwd _ _ _ _ _ _ _ _) as [[af csf] jf]. destruct (ms_copy_bwd _ _ _ _ _ _ _ _) as [[ab ceb] jb].
  cbn [s_exit s_budget]. intros; discriminate.
Qed.
Lemma bigs_exit : forall n ro qoff nb i s, s_exit s = false -> s_exit (ms_bigs n ro qoff nb i s) = true -> s_budget (ms_bigs n ro qoff nb i s) < 0.
Proof.
  induction n; intros ro qoff nb i s E; [cbn [ms_bigs]; rewrite E; intros; discriminate|]. rewrite ms_bigs_S. cbv zeta.
  pose proof (big_exit ro qoff nb i s E) as X. destruct (s_exit (ms_big _ _ _ _ _)) eqn:E1; [intros _; apply X; reflexivity|]. apply IHn. exact E1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma find_orig_spec : forall n a1 i0, 0 <= i0 ->
  (find_orig n a1 i0 = -1 /\ forall i, i0 <= i < i0 + Z.of_nat n -> rd32 a1 i <> 0) \/
  (i0 <= find_orig n a1 i0 < i0 + Z.of_nat n /\ rd32 a1 (find_orig n a1 i0) = 0).
Proof.
  induction n as [|n IH]; intros a1 i0 Hi0; cbn [find_orig]; [left; split; [reflexivity| intros; lia]|].
  destruct (Z.eqb_spec (rd32 a1 i0) 0) as [E|NE]; [right; split; [lia| exact E]|].
  destruct (IH a1 (i0 + 1) ltac:(lia)) as [[A B]|[A B]].
  - left. split; [exact A|]. intros i Hi. destruct (Z.eq_dec i i0) as [->|N]; [exact NE| apply B; lia].
  - right. split; [lia| exact B].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MainSort.
  Variables (a1 a2 ft ro0 bd0 cs ce sl sh sd : zarr) (qoff nb budget : Z).
  Hypothesis BB : zbok a2.
  Hypothesis B1 : zbok a1.
  Hypothesis NB : 1 <= nb <= 1000000.
  Hypothesis QO : nb + 34 <= qoff.

  Lemma BB' : forall i, 0 <= rd8 a2 i < 256. Proof. intros i. unfold rd8. apply BB. Qed.

  (* [comment removed for export] *)
  Lemma mainSort_shape : forall (P : msres -> Prop),
    (forall a2a ft2 x1 a1a ft4 x2 bd ro st,
      ms_radix1 (Z.to_nat nb) a2 (mft1 ft) qoff (nb - 1) (Z.shiftl (rd8 a2 0) 8) = (a2a, ft2, x1) ->
      ms_radix2 (Z.to_nat nb) a1 (ms_overshoot 34 a2a qoff nb 0) (ms_accum 65536 ft2 1) (nb - 1) (Z.shiftl (rd8 (ms_overshoot 34 a2a qoff nb 0) 0) 8) = (a1a, ft4, x2) ->
      ms_ro_init 256 bd0 ro0 0 = (bd, ro) ->
      st = ms_bigs 256 (ms_shell 8 ro ft4 364) qoff nb 0 (MSS a1a (ms_overshoot 34 a2a qoff nb 0) ft4 bd cs ce budget 0 (MQL sl sh sd sl sh sd) false) ->
      P (MSR (s_a1 st) (s_a2 st) (s_ft st) (s_budget st) (ms_shell 8 ro ft4 364) (s_bd st) (s_cs st) (s_ce st) (s_mql st) (s_nqs st))) ->
    P (mainSort a1 a2 ft ro0 bd0 cs ce sl sh sd qoff nb budget).
  Proof.
    intros P H. unfold mainSort.
    match goal with |- context [ms_radix1 ?n ?a ?f ?q ?i ?j] => destruct (ms_radix1 n a f q i j) as [[a2a ft2] x1] eqn:E1 end.
    match goal with |- context [ms_radix2 ?n ?a ?b ?f ?i ?j] => destruct (ms_radix2 n a b f i j) as [[a1a ft4] x2] eqn:E2 end.
    destruct (ms_ro_init 256 bd0 ro0 0) as [bd ro] eqn:E3.
    apply (H a2a ft2 x1 a1a ft4 x2 bd ro _ E1 E2 eq_refl eq_refl).
  Qed.

  Theorem mainSort_post :
    let m := mainSort a1 a2 ft ro0 bd0 cs ce sl sh sd qoff nb budget in
    zbok (mr_ptr m) /\ zbok (mr_block m) /\
    (forall k, 0 <= k < nb -> rd8 (mr_block m) k = rd8 a2 k) /\
    (mr_budget m <? 0 = false -> fm_perm (mr_ptr m) nb /\ PINV a2 nb (mr_ptr m)).
  Proof.
    apply mainSort_shape. intros a2a ft2 x1 a1a ft4 x2 bd ro st E1 E2 E3 Est.
    cbn [mr_ptr mr_block mr_budget].
    pose proof BB' as BBr.
    (* [comment removed for export] *)
    pose proof (radix1_ft a2 nb qoff BBr ltac:(lia) ltac:(lia) a2 ft ltac:(intros; reflexivity)) as R1.
    cbv zeta in R1. rewrite E1 in R1. cbn [fst snd] in R1. destruct R1 as [AG1 FT2].
    pose proof (zbok_radix1 (Z.to_nat nb) a2 (mft1 ft) qoff (nb-1) (Z.shiftl (rd8 a2 0) 8) BB) as ZB2a.
    rewrite E1 in ZB2a. cbn [fst snd] in ZB2a. clear E1.
    set (a2b := ms_overshoot 34 a2a qoff nb 0) in *.
    assert (AG2 : forall k, 0 <= k < nb -> rd8 a2b k = rd8 a2 k).
    { intros k Hk. subst a2b. rewrite (ms_overshoot_low nb qoff ltac:(lia) 34 a2a 0 ltac:(lia) ltac:(cbn; lia) k Hk). apply AG1. exact Hk. }
    assert (ZB2b : zbok a2b) by (subst a2b; apply zbok_overshoot; exact ZB2a).
    pose proof (ms_accum_ft a2 nb BBr ltac:(lia) ft2 FT2) as FT3.
    set (ft3 := ms_accum 65536 ft2 1) in *.
    pose proof (ms_radix_perm a2 nb BBr ltac:(lia) a1 a2b ft3 AG2 FT3) as R2. cbv zeta in R2.
    rewrite E2 in R2. cbn [fst snd] in R2. cps_destruct R2 as (FT4 & KP & PM1 & FR1).
    pose proof (zbok_radix2 (Z.to_nat nb) a1 a2b ft3 (nb-1) (Z.shiftl (rd8 a2b 0) 8) B1) as ZB1a.
    rewrite E2 in ZB1a. cbn [fst snd] in ZB1a. clear E2.
    (* [comment removed for export] *)
    pose proof (runningOrder_perm bd0 ro0 ft4) as ROP. rewrite E3 in ROP. cbv beta iota zeta in ROP.
    cps_destruct ROP as (BD0 & ROR & ROI). clear E3.
    set (ro1 := ms_shell 8 ro ft4 364) in *.
    (* [comment removed for export] *)
    set (s0 := MSS a1a a2b ft4 bd cs ce budget 0 (MQL sl sh sd sl sh sd) false) in *.
    assert (MI0 : MI a2 nb ro1 a2b 0 s0).
    { constructor; subst s0; cbn [s_a1 s_a2 s_ft s_bd s_exit].
      - apply (PINV_of_KpM a2 nb ltac:(lia)). exact KP.
      - intros; reflexivity.
      - intros v Hv. left. apply FT4. exact Hv.
      - intros c Hc. left. apply BD0. exact Hc.
      - intros c Hc. rewrite BD0 by exact Hc. split; [intros X; exfalso; exact (X eq_refl)| cps_intros (i' & Hi' & _); lia].
      - reflexivity. }
    pose proof (ms_bigs_MI a2 nb qoff ro1 BBr ltac:(lia) ltac:(lia) QO ROR ROI a2b AG2 256 0 s0 ltac:(lia) ltac:(cbn; lia) MI0) as MB.
    cbv zeta in MB. rewrite <- Est in MB.
    pose proof (zbok_bigs 256 ro1 qoff nb 0 s0 ltac:(subst s0; exact ZB1a) ltac:(subst s0; exact ZB2b)) as ZBf.
    rewrite <- Est in ZBf. destruct ZBf as [ZBf1 ZBf2].
    pose proof (bigs_exit 256 ro1 qoff nb 0 s0 eq_refl) as EXB. rewrite <- Est in EXB.
    split; [exact ZBf1|]. split; [exact ZBf2|]. split.
    - intros k Hk. destruct MB as [[EX A2]|MIf].
      + rewrite A2 by lia. apply AG2. exact Hk.
      + rewrite (mi_a2 _ _ _ _ _ _ MIf) by lia. apply AG2. exact Hk.
    - intros NEG. destruct MB as [[EX _]|MIf].
      + exfalso. pose proof (EXB EX). apply Z.ltb_ge in NEG. lia.
      + split; [apply (PINV_perm a2 nb BBr ltac:(lia)); exact (mi_pinv _ _ _ _ _ _ MIf)| exact (mi_pinv _ _ _ _ _ _ MIf)].
  Qed.
End MainSort.
