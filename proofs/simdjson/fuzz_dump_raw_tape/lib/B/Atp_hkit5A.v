(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Atp_hkit4A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma nodup_rm : forall (l1 : list (Z * Z)) p n l2, List.NoDup (map fst (l1 ++ (p, n) :: l2)) -> List.NoDup (map fst (l1 ++ l2)).
Proof. intros l1 p n l2 H. rewrite map_app in *. cbn [map fst] in H. exact (NoDup_remove_1 _ _ _ H). Qed.

Lemma six_removes : forall (ia oc idx impl tape sbuf nia noc nidx nimpl ntape nsbuf : Z) (L : list (Z * Z)),
  List.NoDup (map fst ((ia, nia) :: (oc, noc) :: (idx, nidx) :: (impl, nimpl) :: (tape, ntape) :: (sbuf, nsbuf) :: L)) ->
  live_remove impl (live_remove idx (live_remove oc (live_remove ia (live_remove tape (live_remove sbuf
    ((ia, nia) :: (oc, noc) :: (idx, nidx) :: (impl, nimpl) :: (tape, ntape) :: (sbuf, nsbuf) :: L)))))) = L.
Proof.
  intros ia oc idx impl tape sbuf nia noc nidx nimpl ntape nsbuf L H.
  pose proof (live_remove_mid [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl); (tape, ntape)] L sbuf nsbuf H) as E. cbn [app] in E. rewrite E. clear E.
  apply (nodup_rm [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl); (tape, ntape)] sbuf nsbuf L) in H. cbn [app] in H.
  pose proof (live_remove_mid [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl)] L tape ntape H) as E. cbn [app] in E. rewrite E. clear E.
  apply (nodup_rm [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl)] tape ntape L) in H. cbn [app] in H.
  pose proof (live_remove_mid [] ((oc, noc) :: (idx, nidx) :: (impl, nimpl) :: L) ia nia H) as E. cbn [app] in E. rewrite E. clear E.
  apply (nodup_rm [] ia nia _) in H. cbn [app] in H.
  pose proof (live_remove_mid [] ((idx, nidx) :: (impl, nimpl) :: L) oc noc H) as E. cbn [app] in E. rewrite E. clear E.
  apply (nodup_rm [] oc noc _) in H. cbn [app] in H.
  pose proof (live_remove_mid [] ((impl, nimpl) :: L) idx nidx H) as E. cbn [app] in E. rewrite E. clear E.
  apply (nodup_rm [] idx nidx _) in H. cbn [app] in H.
  pose proof (live_remove_mid [] L impl nimpl H) as E. cbn [app] in E. exact E.
Qed.

Lemma seven_removes : forall (copy ia oc idx impl tape sbuf ncopy nia noc nidx nimpl ntape nsbuf : Z) (L : list (Z * Z)),
  List.NoDup (map fst ((copy, ncopy) :: (ia, nia) :: (oc, noc) :: (idx, nidx) :: (impl, nimpl) :: (tape, ntape) :: (sbuf, nsbuf) :: L)) ->
  live_remove impl (live_remove idx (live_remove oc (live_remove ia (live_remove tape (live_remove sbuf (live_remove copy
    ((copy, ncopy) :: (ia, nia) :: (oc, noc) :: (idx, nidx) :: (impl, nimpl) :: (tape, ntape) :: (sbuf, nsbuf) :: L))))))) = L.
Proof.
  intros copy ia oc idx impl tape sbuf ncopy nia noc nidx nimpl ntape nsbuf L H.
  pose proof (live_remove_mid [] _ copy ncopy H) as E. cbn [app] in E. rewrite E. clear E.
  apply (nodup_rm [] copy ncopy _) in H. cbn [app] in H. apply six_removes. exact H.
Qed.

Section Kit5.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma fobj_shadow_client : forall Σ m a n sp x, ART RT Σ m -> fobj RT Σ m a n -> shad a <= x < shad a + (n + 7) / 8 ->
  aclient (rt_live RT Σ) (rt_frames RT Σ) sp x /\ x < rt_sp0 RT Σ - STACK_WIN.
Proof using AF.
  intros Σ m a n sp x HA FO Hx.
  destruct (fobj_shadow_range RT AF Σ m a n HA FO) as (f & c & Hin & S1 & S2 & Q0).
  split; [right; right; right; right; exists f, c; split; [exact Hin| lia]|].
  pose proof (af_frames_range RT AF Σ m f c HA Hin) as (F0 & F1 & _).
  pose proof (af_sp0_win RT AF Σ m HA) as SPW. pose proof (af_sp0_range RT AF Σ m HA) as SPR.
  assert (FSZ : 0 <= fs_size c) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (SH1 : shad (f + fs_size c) <= 17592186044416 + SHB).
  { unfold shad. assert ((f + fs_size c) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; ul). lia. }
  unfold SHB in *. ul.
Qed.

Lemma fobj_pres_ex_stack : forall Σ Σ' live sp d n0 m m' a n, ART RT Σ m -> fobj RT Σ m a n ->
  rt_pres_ex live (rt_frames RT Σ) sp d n0 m m' -> (forall e, In e (rt_live RT Σ) -> In e live) -> rt_frames RT Σ' = rt_frames RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= d -> fobj RT Σ' m' a n.
Proof using AF.
  intros Σ Σ' live sp d n0 m m' a n HA FO PRES SUB FRS DLO.
  apply (fobj_agree RT AF Σ Σ' m m' a n HA FO FRS).
  intros x Hx. cbv beta in Hx. destruct (fobj_shadow_client Σ m a n sp (bv_unsigned x) HA FO Hx) as (CL & XLO).
  apply PRES; [apply (aclient_mono _ _ _ _ _ _ _ CL); [exact SUB| auto| lia]| lia].
Qed.

Lemma live_disj_nth : forall Σ m (i j : nat) p1 n1 p2 n2, ART RT Σ m ->
  nth_error (rt_live RT Σ) i = Some (p1, n1) -> nth_error (rt_live RT Σ) j = Some (p2, n2) -> i <> j -> p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof using AF.
  intros Σ m i j p1 n1 p2 n2 HA Hi Hj NE.
  pose proof Hi as Hi'. apply nth_error_split in Hi'. destruct Hi' as (l1 & l2 & EL & LEN).
  apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 HA EL).
  rewrite EL in Hj. apply in_or_app.
  destruct (Nat.lt_ge_cases j (length l1)) as [LT|GE].
  - left. rewrite nth_error_app1 in Hj by exact LT. exact (nth_error_In _ _ Hj).
  - right. rewrite nth_error_app2 in Hj by exact GE. destruct (j - length l1)%nat as [|q] eqn:EQ; [lia|]. cbn [nth_error] in Hj. exact (nth_error_In _ _ Hj).
Qed.

Lemma fresh_apart_l : forall Σ1 m1 (l1 L : list (Z * Z)) p n usp a,
  ART RT Σ1 m1 -> rt_live RT Σ1 = l1 ++ L -> In (p, n) l1 -> rt_sp0 RT Σ1 - STACK_WIN <= usp -> aclient L (rt_frames RT Σ1) usp a -> ~ (p <= a < p + n).
Proof using AF.
  intros Σ1 m1 l1 L p n usp a ART1 LV INP LOW Ha Hr.
  assert (INP1 : In (p, n) (rt_live RT Σ1)) by (rewrite LV; apply in_or_app; left; exact INP).
  pose proof (af_live_range RT AF Σ1 m1 p n ART1 INP1) as (R0 & R1 & R2).
  destruct Ha as [H|[H|[H|[H|H]]]].
  - lia.
  - pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
  - destruct H as (q & k & Hin & Hq). destruct (in_split _ _ INP) as (la & lb & EL).
    assert (E1 : rt_live RT Σ1 = la ++ (p, n) :: (lb ++ L)) by (rewrite LV, EL, <- app_assoc; reflexivity).
    assert (HIN2 : In (q, k) (la ++ (lb ++ L))) by (apply in_or_app; right; apply in_or_app; right; exact Hin).
    pose proof (af_live_disj RT AF Σ1 m1 p n q k la (lb ++ L) ART1 E1 HIN2). lia.
  - destruct H as (f & k & Hin & Hf).
    pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hin) as (_ & _ & _ & X). specialize (X p n INP1). lia.
  - destruct H as (f & k & Hin & Hf).
    pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hin) as (X & _). specialize (X p n INP1). lia.
Qed.

Lemma not_live_stack : forall Σ m x, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= x -> ~ in_live (rt_live RT Σ) x.
Proof using AF. intros Σ m x HA Hx (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n HA Hin). lia. Qed.

Lemma not_live_frame : forall Σ m f k x, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> f <= x < f + fs_size k -> ~ in_live (rt_live RT Σ) x.
Proof using AF.
  intros Σ m f k x HA Hf Hx (p & n & Hin & Hp). pose proof (af_frames_range RT AF Σ m f k HA Hf) as (_ & _ & _ & X). specialize (X p n Hin). lia.
Qed.

Lemma not_live_fshadow : forall Σ m f k x, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> shad f <= x < shad (f + fs_size k) -> ~ in_live (rt_live RT Σ) x.
Proof using AF.
  intros Σ m f k x HA Hf Hx (p & n & Hin & Hp). pose proof (af_fshadow_apart RT AF Σ m f k HA Hf) as (X & _). specialize (X p n Hin). lia.
Qed.

Lemma not_live_static : forall Σ m x, ART RT Σ m -> client_static x -> ~ in_live (rt_live RT Σ) x.
Proof using AF.
  intros Σ m x HA Hs (p & n & Hin & Hp). pose proof (client_static_range x Hs). pose proof (af_live_range RT AF Σ m p n HA Hin) as (_ & _ & X).
  unfold SEGTOP_A in *. lia.
Qed.

End Kit5.

Lemma outside_of_not_live : forall (live : list (Z * Z)) (W : list (Z * Z)) x,
  (forall r, In r W -> exists p n, In (p, n) live /\ p <= fst r /\ snd r <= p + n) -> ~ in_live live x -> outside W x.
Proof.
  intros live W x HW NL. induction W as [|[l h] W IH]; [exact I|]. cbn [outside]. split.
  - intros Hr. apply NL. destruct (HW (l, h) (or_introl eq_refl)) as (p & n & Hin & P1 & P2). cbn [fst snd] in P1, P2. exists p, n. split; [exact Hin| lia].
  - apply IH. intros r Hr. apply HW. right. exact Hr.
Qed.

Lemma mcost_le : forall n, 0 <= n -> mcost n <= 2 * n + 16384 + 2097152.
Proof. intros n H. unfold mcost, DCOST. destruct (n <=? 64512); lia. Qed.
Lemma mcost_small : forall n, 0 <= n <= 64512 -> mcost n = 2097152.
Proof. intros n H. unfold mcost, DCOST. destruct (Z.leb_spec n 64512); lia. Qed.

