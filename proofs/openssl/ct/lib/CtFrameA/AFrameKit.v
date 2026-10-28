(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition amb (AR : ARun) (FRn : list (Z * nat)) : ARun :=
  mkARun (@ar_RT AR) (@ar_RC AR) (@ar_SP0 AR) (@ar_PMc AR) (@ar_PMc_fdfs AR) (@ar_PMc_ms AR) (@ar_LIBW_cs AR) FRn (@ar_RC2 AR).   (* [comment removed for export] *)
Definition push (AR : ARun) (f : Z) (k : nat) : ARun := amb AR ((f, k) :: @ar_FR AR).

Lemma amb_eta : forall AR : ARun, amb AR (@ar_FR AR) = AR.
Proof. intros [RT RC SP0 PMc H1 H2 H3 FR RC2]. reflexivity. Qed.

Lemma amb_amb : forall AR FR1 FR2, amb (amb AR FR1) FR2 = amb AR FR2.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma AHEAP_eta : forall (AR : ARun) Σ OW LB m, @AHEAP (amb AR (@ar_FR AR)) Σ OW LB m <-> @AHEAP AR Σ OW LB m.
Proof. intros [RT RC SP0 PMc H1 H2 H3 FR RC2] Σ OW LB m. reflexivity. Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation SP0 := (@ar_SP0 AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fr_geo (f : Z) (k : nat) : Prop :=
  0 < f /\ f mod 64 = 0 /\ f + fs_size k <= ACEIL /\ SEGTOP_A <= f /\ (f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f).

Lemma fs_size_pos : forall k, 64 <= fs_size k /\ fs_size k mod 64 = 0.
Proof.
  intros k. unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)) as P.
  split; [nia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma AH_fr_geo : forall Σ OW LB m f k, AHEAP Σ OW LB m -> In (f, k) FR -> fr_geo f k.
Proof.
  intros Σ OW LB m f k H Hin. destruct (AH_fr_range _ _ _ _ f k H Hin) as (R1 & R2 & R3 & R4 & _).
  pose proof (AH_frames _ _ _ _ H) as EF. destruct H as (HA & _). rewrite <- EF in Hin.
  destruct (af_frames_align RT AF Σ m f k HA Hin) as (A1 & A2).
  unfold fr_geo. auto.
Qed.

(* [comment removed for export] *)
Definition in_fr (f : Z) (k : nat) (b : block) : Prop := f <= blk_addr b /\ blk_addr b + blk_size b <= f + fs_size k - 8.
Definition off_fr (f : Z) (k : nat) (b : block) : Prop := blk_addr b + blk_size b <= f \/ f + fs_size k <= blk_addr b.

Lemma AH_fr_blk : forall Σ OW LB m f k b, AHEAP Σ OW LB m -> In (f, k) FR -> In b (OW ++ LB) -> in_fr f k b \/ off_fr f k b.
Proof.
  intros Σ OW LB m f k b H Hf Hb. destruct (AH_cases _ _ _ _ b H Hb) as [HL|((f' & k' & Hf' & P1 & P2) & Hn & _)].
  - right. destruct (AH_fr_range _ _ _ _ f k H Hf) as (_ & _ & _ & _ & R). specialize (R _ _ HL). unfold off_fr. lia.
  - destruct (Z.eq_dec f f') as [E|NE].
    + subst f'. assert (k' = k).
      { pose proof (AH_frames _ _ _ _ H) as EF. destruct H as (HA & _). rewrite <- EF in Hf, Hf'.
        destruct (Nat.eq_dec k' k) as [E|NE]; [exact E|]. exfalso.
        destruct (in_split _ _ Hf) as (l1 & l2 & El).
        assert (Hin2 : In (f, k') (l1 ++ l2)).
        { rewrite El in Hf'. apply in_app_or in Hf'. apply in_or_app. destruct Hf' as [X|[X|X]]; [left; exact X | congruence | right; exact X]. }
        pose proof (af_frames_disj RT AF Σ m f k f k' l1 l2 HA El Hin2) as D.
        pose proof (fs_size_pos k). pose proof (fs_size_pos k'). lia. }
      subst k'. left. split; assumption.
    + right. pose proof (AH_frames _ _ _ _ H) as EF. destruct H as (HA & _). rewrite <- EF in Hf, Hf'.
      destruct (in_split _ _ Hf) as (l1 & l2 & El).
      assert (Hin2 : In (f', k') (l1 ++ l2)).
      { rewrite El in Hf'. apply in_app_or in Hf'. apply in_or_app. destruct Hf' as [X|[X|X]]; [left; exact X | congruence | right; exact X]. }
      pose proof (af_frames_disj RT AF Σ m f k f' k' l1 l2 HA El Hin2) as D. unfold off_fr. lia.
Qed.

(* [comment removed for export] *)
Lemma AH_in_fr_pb : forall Σ OW LB m f k b, AHEAP Σ OW LB m -> In (f, k) FR -> In b (OW ++ LB) -> in_fr f k b -> pb_ok m b.
Proof.
  intros Σ OW LB m f k b H Hf Hb (I1 & I2). destruct (AH_cases _ _ _ _ b H Hb) as [HL|P]; [| exact P]. exfalso.
  destruct (AH_fr_range _ _ _ _ f k H Hf) as (_ & _ & _ & _ & R). specialize (R _ _ HL).
  pose proof (AH_pos_gen _ _ _ _ b H Hb). lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pb_ok_push : forall m b f k, @pb_ok AR m b -> @pb_ok (push AR f k) m b.
Proof.
  intros m b f k ((f' & k' & Hin & P1 & P2) & Hn & W & AC). split; [| exact (conj Hn (conj W AC))].
  exists f', k'. split; [right; exact Hin | split; assumption].
Qed.

Lemma AH_enter : forall Σ Σ1 OW LB m m1 f k SP,
  AHEAP Σ OW LB m -> ART RT Σ1 m1 -> rt_frames RT Σ1 = (f, k) :: rt_frames RT Σ -> rt_live RT Σ1 = rt_live RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_pres (rt_live RT Σ) (rt_frames RT Σ) SP m m1 ->
  wr_at ctasegs m1 f (fs_size k - 8) -> wr_at ctasegs m1 (shad f) (fs_size k / 8) ->
  @BnHeapA.AHEAP (push AR f k) Σ1 OW LB m1 /\ (forall b, In b (OW ++ LB) -> off_fr f k b).
Proof.
  intros Σ Σ1 OW LB m m1 f k SP H HA1 HF1 HL1 HS1 PRES W1 W2.
  pose proof H as (HA & HS & HFr & SPL & ND & F1 & F2).
  rewrite HFr in PRES, HF1. pose proof (fr_agree_of_rt_pres _ _ _ _ PRES) as AG.
  destruct (heap_split_agree _ _ _ _ _ SPL AG) as (FW & PB & LBr & P1 & P2 & FP & AP).
  split.
  - split; [exact HA1|]. split; [rewrite HS1; exact HS|]. split; [exact HF1|]. split; [| exact (conj ND (conj F1 F2))].
    split.
    + unfold fr_wr. cbn [ar_FR push amb]. constructor; [cbn [fst snd]; split; assumption | exact FW].
    + exists PB, LBr. split; [exact P1|]. split; [rewrite HL1; exact P2|]. split; [| exact AP].
      eapply Forall_impl; [| exact FP]. intros b Hb. exact (pb_ok_push m1 b f k Hb).
  - intros b Hb. assert (Hf1 : In (f, k) (rt_frames RT Σ1)) by (rewrite HF1; left; reflexivity).
    destruct (af_frames_range RT AF Σ1 m1 f k HA1 Hf1) as (_ & _ & _ & R).
    destruct (AH_cases _ _ _ _ b H Hb) as [HL|((f' & k' & Hf' & Q1 & Q2) & Hn & _)].
    + rewrite <- HL1 in HL. specialize (R _ _ HL). unfold off_fr. lia.
    + pose proof (af_frames_disj RT AF Σ1 m1 f k f' k' [] FR HA1 ltac:(rewrite HF1; reflexivity) Hf') as D. unfold off_fr. lia.
Qed.

End WithRT.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Frame.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition fr_write_ok (L : list block) (f : Z) (k : nat) (iv : Z * Z) : Prop :=
  aclient_write_ok L iv \/ (f <= fst iv /\ snd iv <= f + fs_size k - 8) \/ (shad f <= fst iv /\ snd iv <= shad f + fs_size k / 8).

Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

Lemma shad_fr_end : forall f k, shad (f + fs_size k) = shad f + fs_size k / 8.
Proof.
  intros f k. unfold shad. destruct (fs_size_div8 k) as (E & _). rewrite E at 1.
  replace (f + 8 * (fs_size k / 8)) with (f + (fs_size k / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma off_fr_shadow : forall f k b i, f mod 8 = 0 -> 0 <= blk_addr b -> off_fr f k b -> 0 <= i < blk_size b ->
  shad (blk_addr b + i) < shad f \/ shad f + fs_size k / 8 <= shad (blk_addr b + i).
Proof.
  intros f k b i F8 B0 [O|O] Hi.
  - left. unfold shad. assert ((blk_addr b + i) / 8 < f / 8); [| lia].
    apply Z.div_lt_upper_bound; [lia|]. assert (E : f = 8 * (f / 8)) by (pose proof (Z.div_mod f 8 ltac:(lia)); lia). lia.
  - right. rewrite <- shad_fr_end. apply shad_mono. lia.
Qed.

Lemma AH_frame_fr : forall Σ OW LB m m' W f k,
  In (f, k) FR -> AHEAP Σ OW LB m -> munch W m m' -> wmono ctasegs m m' ->
  Forall (fr_write_ok (OW ++ LB) f k) W -> (forall b, In b LB -> off_fr f k b) -> AHEAP Σ OW LB m'.
Proof.
  intros Σ OW LB m m' W f k Hf H MU WM HW OFF. pose proof H as (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & FP & AP) & Rest).
  destruct (AH_fr_geo _ _ _ _ f k H Hf) as (G1 & G2 & G3 & G4 & G5). pose proof (AH_ceil _ _ _ _ H) as (C1 & C2 & C3).
  split; [| split; [exact HS | split; [exact HFr | split; [| exact Rest]]]].
  - apply (af_frame RT AF Σ m m' ACEIL HA); [unfold BnHeapA.ACEIL; rewrite HS; lia | | exact WM].
    intros a Hna. apply MU. rewrite HFr in Hna.
    clear - H HW Hna Hf. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|].
    apply Forall_cons_iff in HW as [H1 H2]. split; [| exact (IH H2)].
    intros [L1 L2]. apply Hna. destruct H1 as [H1|[[X1 X2]|[X1 X2]]]; cbn [fst snd] in *.
    + apply (AH_aclient _ _ _ _ ACEIL _ H).
      destruct H1 as [[D1 D2]|[D|(b & Hb & D1 & D2)]]; cbn [fst snd] in *.
      * left. lia.
      * right; left. apply D. lia.
      * right; right. exists b. split; [exact Hb | lia].
    + right; right; right; left. exists f, k. split; [exact Hf | lia].
    + right; right; right; right. exists f, k. split; [exact Hf |]. rewrite shad_fr_end. lia.
  - split; [exact (fr_wr_wmono m m' FW WM)|]. exists PB, LBr. split; [exact P1|]. split; [exact P2|]. split; [| exact AP].
    apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) FP b Hb) as PK. destruct PK as (PI & Hn & WR & AC).
    split; [exact PI|]. split; [exact Hn|]. split; [exact (wr_at_transport ctasegs m m' _ _ WR WM)|].
    assert (HbL : In b LB) by (eapply Permutation_in; [symmetry; exact P1 | apply in_or_app; left; exact Hb]).
    assert (B0 : 0 < blk_addr b) by (destruct PI as (f' & k' & Hf' & Q1 & Q2); destruct (AH_fr_range _ _ _ _ f' k' H Hf') as (R1 & _); lia).
    eapply acc_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | exact AC |].
    intros i Hi. pose proof (pb_shadow_range _ _ _ _ b i H PI Hi) as SR.
    pose proof (off_fr_shadow f k b i ltac:(clear - G2; Z.div_mod_to_equations; lia) ltac:(lia) (OFF b HbL) Hi) as SO.
    clear - HW SR SO H G1 G3 G4 G5 C1 C2 C3 Hf. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|].
    apply Forall_cons_iff in HW as [H1 H2]. split; [| exact (IH H2)].
    intros [L1 L2]. destruct H1 as [H1|[[X1 X2]|[X1 X2]]]; cbn [fst snd] in *.
    + destruct H1 as [[D1 D2]|[D|(b' & Hb' & D1 & D2)]]; cbn [fst snd] in *.
      * unfold SHHI in *. lia.
      * destruct (D _ (conj L1 L2)) as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
        unfold SHLO in SR. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
      * pose proof (AH_offsh _ _ _ _ b' H Hb') as O. lia.
    + unfold SHLO, SHHI in SR. lia.
    + lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma frame_obj_open : forall Σ OW LB m f k q A n,
  In (f, k) FR -> AHEAP Σ OW LB m -> f <= A -> A + n <= f + fs_size k - 8 -> 0 < n -> acc ctasegs m A n ->
  ~ In q (map blk_id (OW ++ LB)) -> (forall b, In b LB -> blk_apart (q, A, n) b) ->
  AHEAP Σ OW ((q, A, n) :: LB) m.
Proof.
  intros Σ OW LB m f k q A n Hf H A1 A2 Hn AC Hq AP0. pose proof H as (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & FP & AP) & ND & F1 & F2).
  destruct (AH_fr_wr _ _ _ _ f k H Hf) as ((W0 & W1 & W2) & _).
  split; [exact HA|]. split; [exact HS|]. split; [exact HFr|]. split.
  - split; [exact FW|]. exists ((q, A, n) :: PB), LBr. split; [cbn [app]; apply perm_skip; exact P1|]. split; [exact P2|].
    split.
    + constructor; [| exact FP]. split; [exists f, k; cbn [blk_addr blk_size fst snd]; split; [exact Hf | lia]|].
      cbn [blk_addr blk_size fst snd]. split; [exact Hn|]. split; [| exact AC].
      split; [lia|]. split; [lia|]. intros i Hi. replace (A + i) with (f + (A - f + i)) by lia. apply W2. lia.
    + cbn [apartl]. split; [| exact AP]. apply Forall_forall. intros b Hb. apply AP0.
      eapply Permutation_in; [symmetry; exact P1 | apply in_or_app; left; exact Hb].
  - split.
    + assert (E : map blk_id (OW ++ (q, A, n) :: LB) = map blk_id OW ++ q :: map blk_id LB) by (rewrite map_app; reflexivity).
      rewrite E. apply NoDup_Add with (a := q) (l := map blk_id OW ++ map blk_id LB); [apply Add_app|].
      rewrite <- map_app. split; [exact ND | exact Hq].
    + split; [exact F1|]. constructor; [exact Hn | exact F2].
Qed.

Lemma apartl_perm : forall l l', Permutation l l' -> apartl l -> apartl l'.
Proof.
  intros l l' P. induction P as [| x l l' P IH | x y l | l1 l2 l3 P1 IH1 P2 IH2]; intros H.
  - exact I.
  - cbn [apartl] in *. destruct H as [F A]. split; [| exact (IH A)]. eapply Permutation_Forall; [exact P | exact F].
  - cbn [apartl] in *. destruct H as [Fy [Fx A]]. apply Forall_cons_iff in Fy as [Hyx Fy].
    split; [constructor; [unfold blk_apart in *; lia | exact Fx]|]. split; [exact Fy | exact A].
  - exact (IH2 (IH1 H)).
Qed.

(* [comment removed for export] *)
Lemma frame_obj_close : forall Σ OW LB m f k b,
  In (f, k) FR -> AHEAP Σ OW (b :: LB) m -> in_fr f k b -> AHEAP Σ OW LB m.
Proof.
  intros Σ OW LB m f k b Hf H IN. pose proof H as (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & FP & AP) & ND & F1 & F2).
  assert (HbP : In b PB).
  { assert (X : In b (PB ++ LBr)) by (eapply Permutation_in; [exact P1 | left; reflexivity]).
    apply in_app_or in X as [X|X]; [exact X|]. exfalso.
    assert (HL : In (blk_addr b, blk_size b) (rt_live RT Σ)).
    { eapply Permutation_in; [symmetry; exact P2|]. apply in_map_iff. exists b. split; [reflexivity | apply in_or_app; right; exact X]. }
    destruct (AH_fr_range _ _ _ _ f k H Hf) as (_ & _ & _ & _ & R). specialize (R _ _ HL).
    pose proof (AH_pos_gen _ _ _ _ b H (in_or_app OW (b :: LB) b (or_intror (in_eq b LB)))). destruct IN as (I1 & I2). lia. }
  destruct (in_split _ _ HbP) as (p1 & p2 & EP).
  assert (PP : Permutation PB (b :: p1 ++ p2)) by (rewrite EP; symmetry; apply Permutation_middle).
  assert (P1' : Permutation LB ((p1 ++ p2) ++ LBr)).
  { apply (Permutation_cons_inv (a := b)). eapply Permutation_trans; [exact P1|]. cbn [app].
    change (b :: (p1 ++ p2) ++ LBr) with ((b :: p1 ++ p2) ++ LBr). apply Permutation_app_tail. exact PP. }
  split; [exact HA|]. split; [exact HS|]. split; [exact HFr|]. split.
  - split; [exact FW|]. exists (p1 ++ p2), LBr. split; [exact P1'|]. split; [exact P2|].
    pose proof (Permutation_Forall PP FP) as FP'. apply Forall_cons_iff in FP' as [_ FP'].
    pose proof (apartl_perm _ _ PP AP) as AP'. cbn [apartl] in AP'. split; [exact FP' | exact (proj2 AP')].
  - split.
    + rewrite map_app in ND |- *. cbn [map] in ND. apply NoDup_remove_1 in ND. exact ND.
    + split; [exact F1|]. apply Forall_cons_iff in F2 as [_ F2]. exact F2.
Qed.

End Frame.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section ShadowCells.

Lemma bytes_at_skipn : forall (m : mem) a bs k, bytes_at ctasegs m a bs -> (k <= length bs)%nat -> bytes_at ctasegs m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros m a bs k H Hk. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by exact Hk. exact H.
Qed.

Lemma bytes_at_firstn : forall (m : mem) a bs k, bytes_at ctasegs m a bs -> bytes_at ctasegs m a (firstn k bs).
Proof. intros m a bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [H _]. exact H. Qed.

(* [comment removed for export] *)
Lemma acc_of_shadow_cells : forall (m : mem) S cs k a n,
  rw_cells ctasegs m S cs -> a mod 8 = 0 -> 0 <= a -> 0 <= n -> shad a = S + Z.of_nat k -> (k <= length (cells_bytes cs))%nat ->
  firstn (length (ushadow n)) (skipn k (cells_bytes cs)) = ushadow n ->
  acc ctasegs m a n.
Proof.
  intros m S cs k a n [[_ HB] _] A8 A0 N0 ES HK E. apply (acc_ushadow ctasegs m a n A8 A0 N0).
  rewrite ES, <- E. apply bytes_at_firstn. apply bytes_at_skipn; assumption.
Qed.

End ShadowCells.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Leave.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).

Lemma pb_ok_pop : forall Σ OW LB m b f k, @BnHeapA.AHEAP (push AR f k) Σ OW LB m -> @pb_ok (push AR f k) m b -> off_fr f k b -> @pb_ok AR m b.
Proof.
  intros Σ OW LB m b f k H ((f' & k' & Hin & P1 & P2) & Hn & W & AC) OFF. split; [| exact (conj Hn (conj W AC))].
  destruct Hin as [E|Hin]; [| exists f', k'; split; [exact Hin | split; assumption]].
  exfalso. injection E as <- <-. pose proof (fs_size_pos k). unfold off_fr in OFF. lia.
Qed.

(* [comment removed for export] *)
Lemma frame_release_cells : forall Σ OW LB m f k,
  @BnHeapA.AHEAP (push AR f k) Σ OW LB m -> (forall b, In b LB -> off_fr f k b) ->
  exists fl, rw_cells ctasegs m fl [C1 (Z_to_bv 8 1)] /\ ro_cells ctasegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 fl)]
    /\ 0 < fl /\ fl + 1 <= ACEIL /\ (fl + 1 <= f \/ f + fs_size k <= fl) /\ (fl + 1 <= 0x10000 \/ SEGTOP_A <= fl)
    /\ (fl + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= fl)
    /\ (forall b, In b (OW ++ LB) -> fl < blk_addr b \/ blk_addr b + blk_size b <= fl)
    /\ forall m', munch [(fl, fl + 1)] m m' -> wmono ctasegs m m' -> rw_cells ctasegs m' fl [C1 (Z_to_bv 8 0)] ->
         exists Σ', @BnHeapA.AHEAP AR Σ' OW LB m' /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_allow RT Σ' = rt_allow RT Σ
                    /\ (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo).
Proof.
  intros Σ OW LB m f k H OFF. pose proof H as (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & FP & AP) & ND & F1 & F2).
  cbn [ar_FR ar_RT ar_SP0 push amb] in HFr, HS.
  destruct (af_frame_release RT AF Σ m f k FR HA HFr) as (Σ' & fl & C1 & NC & L0 & L1 & L2 & L3 & L4 & C2 & REL).
  exists fl. split; [exact C1|]. split; [exact C2|]. split; [exact L0|].
  split; [unfold BnHeapA.ACEIL; rewrite <- HS; exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
  split.
  { intros b Hb. destruct (Z_lt_dec fl (blk_addr b)) as [X|X]; [left; exact X|]. destruct (Z_le_dec (blk_addr b + blk_size b) fl) as [Y|Y]; [right; exact Y|].
    exfalso. apply NC. rewrite HFr. change ((f, k) :: FR) with (@ar_FR (push AR f k)).
    apply (@AH_aclient (push AR f k) Σ OW LB m USTACK_TOP fl H). right; right. exists b. split; [exact Hb | lia]. }
  intros m' MU WM CF. destruct (REL m' MU WM CF) as (ART' & EF' & EL' & ES' & EC' & EA' & EM').
  exists Σ'. split; [| exact (conj EC' (conj EA' EM'))].
  split; [exact ART'|]. split; [rewrite ES'; exact HS|]. split; [exact EF'|]. split; [| exact (conj ND (conj F1 F2))].
  split.
  - unfold fr_wr in FW |- *. cbn [ar_FR push amb] in FW. apply Forall_cons_iff in FW as [_ FW].
    eapply Forall_impl; [| exact FW]. intros [f' k'] [X1 X2]. cbn [fst snd] in *. split; eapply wr_at_transport; eassumption.
  - exists PB, LBr. split; [exact P1|]. split; [rewrite EL'; exact P2|]. split; [| exact AP].
    apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) FP b Hb) as PK.
    assert (HbL : In b LB) by (eapply Permutation_in; [symmetry; exact P1 | apply in_or_app; left; exact Hb]).
    pose proof (pb_ok_pop Σ OW LB m b f k H PK (OFF b HbL)) as (PI & Hn & WR & AC).
    split; [exact PI|]. split; [exact Hn|]. split; [exact (wr_at_transport ctasegs m m' _ _ WR WM)|].
    eapply acc_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | exact AC |].
    intros i Hi. cbn [outside]. split; [| exact I].
    destruct PK as (PI' & _). pose proof (@pb_shadow_range (push AR f k) Σ OW LB m b i H PI' Hi) as SR. unfold SHLO, SHHI in SR. lia.
Qed.

End Leave.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fr_depth_ok {AR : ARun} (d : nat) : Prop := (length (@ar_FR AR) + d <= FRAMES_MAX)%nat.
Lemma fr_depth_push : forall {AR : ARun} d f k, fr_depth_ok (S d) -> (length (@ar_FR AR) < FRAMES_MAX)%nat /\ @fr_depth_ok (push AR f k) d.
Proof. intros AR d f k H. unfold fr_depth_ok in *. cbn [ar_FR push amb length]. lia. Qed.
Lemma fr_depth_le : forall {AR : ARun} d d', fr_depth_ok d -> (d' <= d)%nat -> fr_depth_ok d'.
Proof. intros AR d d' H L. unfold fr_depth_ok in *. lia. Qed.
