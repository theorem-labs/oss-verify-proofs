(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma live_remove_sub : forall (l : list (Z * Z)) p e, In e (live_remove p l) -> In e l.
Proof.
  intros l p e He. unfold live_remove in He. apply stdpp.base.list_elem_of_In in He.
  apply stdpp.list_basics.list.list_elem_of_filter in He. apply stdpp.base.list_elem_of_In. exact (proj2 He).
Qed.

Lemma live_remove_keep : forall (l : list (Z * Z)) p e, In e l -> fst e <> p -> In e (live_remove p l).
Proof.
  intros l p e He Hp. unfold live_remove. apply stdpp.base.list_elem_of_In. apply stdpp.list_basics.list.list_elem_of_filter.
  split; [| apply stdpp.base.list_elem_of_In; exact He]. apply Z.eqb_neq in Hp. rewrite Hp. exact I.
Qed.

Lemma live_remove_none : forall (l : list (Z * Z)) p, (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
  induction l as [|e l IH]; intros p H; [reflexivity|]. unfold live_remove in *.
  pose proof (H e (or_introl eq_refl)) as Hp. apply Z.eqb_neq in Hp.
  rewrite stdpp.list_basics.list.filter_cons_True by (rewrite Hp; exact I).
  f_equal. apply IH. intros e' He'. apply H. right. exact He'.
Qed.

Lemma live_remove_hd : forall (l : list (Z * Z)) p n, (forall e, In e l -> fst e <> p) -> live_remove p ((p, n) :: l) = l.
Proof.
  intros l p n H. unfold live_remove.
  rewrite stdpp.list_basics.list.filter_cons_False by (cbn [fst]; rewrite Z.eqb_refl; intros X; exact X).
  exact (live_remove_none l p H).
Qed.

Lemma shz_of_zero_run : forall (m : mem) a k, a mod 8 = 0 -> 0 <= a ->
  bytes_at bsegs m (shad a) (repeat z8 k) -> shz m a (8 * Z.of_nat k).
Proof.
  intros m a k A8 A0 HB. pose proof (acc_zero_run bsegs m a k A8 A0 HB) as AC.
  pose proof (shz_of_acc m a _ AC A8 A0) as S. replace (8 * Z.of_nat k / 8) with (Z.of_nat k) in S; [exact S|].
  rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Section HKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Lemma ASTA_switch : forall (Σ Σ' : rts RT) PMc Pm c, ASTA RT Σ PMc Pm c -> rt_allow RT Σ' = rt_allow RT Σ ->
  (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> ASTA RT Σ' PMc Pm c.
Proof.
  intros Σ Σ' PMc Pm c H HA HM. unfold ASTA in *. rewrite HA.
  eapply AST_conseq; [exact H| auto|]. intros mo [H1 H2]. split; [apply HM; exact H1| exact H2].
Qed.

Lemma fframe_ranges : forall Σ m f c, ART RT Σ m -> In (f, c) (rt_frames RT Σ) ->
  0 < f /\ f + fs_size c <= rt_sp0 RT Σ - STACK_WIN /\ 0 <= fs_size c
  /\ SHB <= shad f /\ shad (f + fs_size c) + 1 <= rt_sp0 RT Σ - STACK_WIN.
Proof using AF.
  intros Σ m f c HA Hin. pose proof (af_frames_range RT AF Σ m f c HA Hin) as (F0 & F1 & _).
  pose proof (af_sp0_win RT AF Σ m HA) as SPW. pose proof (af_sp0_range RT AF Σ m HA) as SPR.
  assert (FSZ : 0 <= fs_size c) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  split; [exact F0|]. split; [exact F1|]. split; [exact FSZ|].
  split; [unfold shad; assert (0 <= f / 8) by (apply Z.div_pos; lia); lia|].
  unfold shad. assert ((f + fs_size c) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; ul). ul.
Qed.

Definition fobj (Σ : rts RT) (m : mem) (a n : Z) : Prop :=
  a mod 8 = 0 /\ 0 <= n /\ (exists f c, In (f, c) (rt_frames RT Σ) /\ f <= a /\ a + 8 * ((n + 7) / 8) <= f + fs_size c - 8)
  /\ bytes_at bsegs m (shad a) (repeat z8 (Z.to_nat ((n + 7) / 8))).

Lemma fobj_shz : forall Σ m a n, ART RT Σ m -> fobj Σ m a n -> shz m a n.
Proof using AF.
  intros Σ m a n HA (A8 & N0 & (f & c & Hin & FL & FH) & HB).
  pose proof (fframe_ranges Σ m f c HA Hin) as (F0 & _).
  assert (Q0 : 0 <= (n + 7) / 8) by (apply Z.div_pos; lia).
  eapply shz_sub; [exact (shz_of_zero_run m a _ A8 ltac:(lia) HB)| lia|].
  rewrite Z2Nat.id by lia. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia.
Qed.

Lemma fobj_shadow_range : forall Σ m a n, ART RT Σ m -> fobj Σ m a n ->
  exists f c, In (f, c) (rt_frames RT Σ) /\ shad f <= shad a /\ shad a + (n + 7) / 8 <= shad (f + fs_size c) /\ 0 <= (n + 7) / 8.
Proof using AF.
  intros Σ m a n HA (A8 & N0 & (f & c & Hin & FL & FH) & HB). exists f, c. split; [exact Hin|].
  pose proof (fframe_ranges Σ m f c HA Hin) as (F0 & _ & FSZ & _).
  assert (Q0 : 0 <= (n + 7) / 8) by (apply Z.div_pos; lia).
  unfold shad. split; [pose proof (Z.div_le_mono f a 8 ltac:(lia) FL); lia|]. split; [| exact Q0].
  pose proof (Z.div_mod a 8 ltac:(lia)) as DA. rewrite A8 in DA.
  assert (a / 8 + (n + 7) / 8 <= (f + fs_size c) / 8); [| lia].
  apply Z.div_le_lower_bound; lia.
Qed.

Definition fp_client (Σ : rts RT) (lo : Z) (W : list (Z * Z)) : Prop :=
  Forall (fun r => (lo <= fst r /\ snd r <= USTACK_TOP) \/ (exists p k, In (p, k) (rt_live RT Σ) /\ p <= fst r /\ snd r <= p + k)
                   \/ (exists f c, In (f, c) (rt_frames RT Σ) /\ f <= fst r /\ snd r <= f + fs_size c - 8)) W.

Lemma art_fp_client : forall Σ (m m' : mem) lo W, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> fp_client Σ lo W ->
  munch W m m' -> wmono bsegs m m' -> ART RT Σ m'.
Proof using AF.
  intros Σ m m' lo W HA LO FP MU WM. apply (art_client_write RT AF Σ m m' lo HA LO); [| exact WM].
  intros a Ha. apply MU. clear MU. induction W as [|[wl wh] W IH]; [exact I|]. inversion FP as [|? ? H1 H2]; subst.
  cbn [outside]. split; [| exact (IH H2)]. intros Hin. apply Ha. cbn [fst snd] in H1.
  destruct H1 as [H1|[(p & k & Hp & P1 & P2)|(f & c & Hf & P1 & P2)]].
  - left. lia.
  - right; right; left. exists p, k. split; [exact Hp| lia].
  - right; right; right; left. exists f, c. split; [exact Hf| lia].
Qed.

Lemma fobj_munch : forall Σ m m' lo W a n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> fp_client Σ lo W ->
  munch W m m' -> fobj Σ m a n -> fobj Σ m' a n.
Proof using AF.
  intros Σ m m' lo W a n HA LO FP MU FO.
  destruct (fobj_shadow_range Σ m a n HA FO) as (f & c & Hin & S1 & S2 & Q0).
  destruct FO as (A8 & N0 & FR & HB). split; [exact A8|]. split; [exact N0|]. split; [exact FR|].
  pose proof (fframe_ranges Σ m f c HA Hin) as (F0 & F1 & FSZ & S0 & S3).
  pose proof (af_fshadow_apart RT AF Σ m f c HA Hin) as (AL & AFR).
  assert (DJ : disjoint_from W (shad a) ((n + 7) / 8)).
  { clear MU HB. induction W as [|[wl wh] W IH]; [exact I|]. inversion FP as [|? ? H1 H2]; subst. cbn [disjoint_from].
    split; [| exact (IH H2)].
    cbn [fst snd] in H1. destruct H1 as [H1|[(p & k & Hp & P1 & P2)|(f' & c' & Hf & P1 & P2)]].
    - left. lia.
    - destruct (AL p k Hp); lia.
    - destruct (AFR f' c' Hf); lia. }
  apply (bytes_at_transport bsegs W m m' _ _ HB MU). rewrite repeat_length, Z2Nat.id by lia. exact DJ.
Qed.

Lemma fobj_pres : forall Σ Σ' live sp m m' a n, ART RT Σ m -> fobj Σ m a n ->
  rt_pres live (rt_frames RT Σ) sp m m' -> rt_frames RT Σ' = rt_frames RT Σ -> fobj Σ' m' a n.
Proof using AF.
  intros Σ Σ' live sp m m' a n HA FO PRES FRS.
  destruct (fobj_shadow_range Σ m a n HA FO) as (f & c & Hin & S1 & S2 & Q0).
  destruct FO as (A8 & N0 & FR & HB). split; [exact A8|]. split; [exact N0|]. split; [rewrite FRS; exact FR|].
  apply (bytes_at_agree bsegs m m' _ _ HB). apply (agree_of_pres _ _ _ _ _ _ PRES).
  intros x Hx. rewrite repeat_length, Z2Nat.id in Hx by lia.
  right; right; right; right. exists f, c. split; [exact Hin| lia].
Qed.

Lemma fobj_agree : forall Σ Σ' m m' a n, ART RT Σ m -> fobj Σ m a n -> rt_frames RT Σ' = rt_frames RT Σ ->
  agree_on (fun x => shad a <= x < shad a + (n + 7) / 8) m m' -> fobj Σ' m' a n.
Proof using AF.
  intros Σ Σ' m m' a n HA FO FRS AG.
  destruct (fobj_shadow_range Σ m a n HA FO) as (f & c & Hin & S1 & S2 & Q0).
  destruct FO as (A8 & N0 & FR & HB). split; [exact A8|]. split; [exact N0|]. split; [rewrite FRS; exact FR|].
  apply (bytes_at_agree bsegs m m' _ _ HB). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *.
  rewrite repeat_length, Z2Nat.id in Hx by lia. exact Hx.
Qed.

Lemma newframe_apart : forall (Σ Σ1 : rts RT) (m1 : mem) Fr k usp a,
  ART RT Σ1 m1 -> rt_frames RT Σ1 = (Fr, k) :: rt_frames RT Σ -> rt_live RT Σ1 = rt_live RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
  ~ (Fr <= a < Fr + fs_size k) /\ ~ (shad Fr <= a < shad (Fr + fs_size k)).
Proof using AF.
  intros Σ Σ1 m1 Fr k usp a ART1 FRS LV SP0 LU Ha.
  assert (INF : In (Fr, k) (rt_frames RT Σ1)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m1 Fr k ART1 INF) as (R0 & R1 & R2 & R3).
  pose proof (af_fshadow_apart RT AF Σ1 m1 Fr k ART1 INF) as (SL & SF).
  pose proof (af_sp0_range RT AF Σ1 m1 ART1) as SPR. pose proof (af_sp0_win RT AF Σ1 m1 ART1) as SPW.
  rewrite SP0 in R1, SPR, SPW.
  assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (SH1 : shad (Fr + fs_size k) <= 17592186044416 + SHB).
  { unfold shad. assert ((Fr + fs_size k) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; ul). lia. }
  assert (SH0 : SHB <= shad Fr) by (unfold shad; assert (0 <= Fr / 8) by (apply Z.div_pos; lia); lia).
  assert (SHM : shad Fr <= shad (Fr + fs_size k)) by (unfold shad; pose proof (Z.div_le_mono Fr (Fr + fs_size k) 8 ltac:(lia) ltac:(lia)); lia).
  destruct Ha as [H|[H|[H|[H|H]]]].
  - split; ul.
  - pose proof (client_static_range a H). split; [destruct R2; unfold SEGTOP_A in *; lia|]. ul.
  - destruct H as (p & n & Hin & Hp). rewrite <- LV in Hin. destruct (R3 p n Hin); destruct (SL p n Hin); split; lia.
  - destruct H as (f & k' & Hin & Hf).
    destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D];
      (destruct (SF f k' ltac:(rewrite FRS; right; exact Hin)) as [E|E]); split; lia.
  - destruct H as (f & k' & Hin & Hf).
    assert (INf : In (f, k') (rt_frames RT Σ1)) by (rewrite FRS; right; exact Hin).
    pose proof (af_fshadow_apart RT AF Σ1 m1 f k' ART1 INf) as (_ & SF').
    destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D].
    + pose proof (Z.div_le_mono (Fr + fs_size k) f 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
    + assert (FSZ' : 0 <= fs_size k') by (unfold fs_size; apply Z.shiftl_nonneg; lia).
      pose proof (Z.div_le_mono (f + fs_size k') Fr 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
Qed.

End HKit.

Ltac pres_tac :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbv beta in Hx; cbn [cells_size csize Nat.add] in Hx;
  first [ left; unfold USTACK_TOP in *; lia
        | right; right; left; eexists _, _; split; [eassumption| lia]
        | right; right; right; left; eexists _, _; split; [eassumption| lia] ].
