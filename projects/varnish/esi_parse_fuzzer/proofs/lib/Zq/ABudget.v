(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AInvWfp.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sec_n_sum (chunks : list chunkS) : Z := fold_right (fun s acc => cs_n s + acc) 0 chunks.
Definition qsum (E : list qentry) : Z := fold_right (fun e acc => qe_n e + acc) 0 E.

Lemma sec_n_sum_cons : forall s l, sec_n_sum (s :: l) = cs_n s + sec_n_sum l. Proof. reflexivity. Qed.
Lemma qsum_cons : forall e l, qsum (e :: l) = qe_n e + qsum l. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma qsum_app : forall l1 l2, qsum (l1 ++ l2) = qsum l1 + qsum l2.
Proof. induction l1 as [|e l1 IH]; intros l2; [reflexivity|]. cbn [app]. rewrite !qsum_cons, IH. lia. Qed.
Lemma qsum_nonneg : forall E, (forall e, In e E -> 0 <= qe_n e) -> 0 <= qsum E.
Proof. induction E as [|e E IH]; intros H; [reflexivity|]. rewrite qsum_cons. pose proof (H e (or_introl eq_refl)). specialize (IH ltac:(intros; apply H; right; assumption)). lia. Qed.

Lemma as_livebytes_delete : forall (lm : gmap Z liveinfo) u li,
  lm !! u = Some li -> as_livebytes_ lm = li_n li + as_livebytes_ (delete u lm).
Proof.
  intros lm u li Hu. unfold as_livebytes_. rewrite (map_fold_delete_L _ _ u li lm); [reflexivity| | exact Hu].
  intros j1 j2 z1 z2 y _ _ _. lia.
Qed.
Lemma as_livebytes_nonneg : forall (lm : gmap Z liveinfo),
  (forall u li, lm !! u = Some li -> 0 <= li_n li) -> 0 <= as_livebytes_ lm.
Proof.
  intros lm. unfold as_livebytes_.
  apply (map_fold_weak_ind (fun r m => (forall u li, m !! u = Some li -> 0 <= li_n li) -> 0 <= r)).
  - intros _. lia.
  - intros i x m r Hi IH H. assert (0 <= li_n x) by (apply (H i); rewrite lookup_insert_eq; reflexivity).
    assert (0 <= r). { apply IH. intros u li Hu. apply (H u). rewrite lookup_insert_ne; [exact Hu|]. intros ->. rewrite Hi in Hu. discriminate. }
    lia.
Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma sec_sum_bound : forall (chunks : list chunkS) (lm : gmap Z liveinfo) (E : list qentry),
  NoDup chunks ->
  (forall u li, lm !! u = Some li -> 0 <= li_n li) ->
  (forall e, In e E -> 0 <= qe_n e /\ (forall mb n0, qe_chunk e = ChS (CS mb n0) -> n0 = qe_n e /\ 64512 < qe_n e)) ->
  (forall s, In s chunks -> (exists u, lm !! u = Some (LI (ChS s) (cs_n s))) \/ In (ChS s) (map qe_chunk E)) ->
  (forall s, In s chunks -> 64512 < cs_n s) ->
  sec_n_sum chunks <= as_livebytes_ lm + qsum E /\
  64513 * Z.of_nat (length chunks) <= 64513 * Z.of_nat (size lm) + qsum E.
Proof.
  induction chunks as [|s rest IH]; intros lm E ND LN EN COV BIG.
  - cbn. pose proof (as_livebytes_nonneg lm LN). pose proof (qsum_nonneg E ltac:(intros e He; exact (proj1 (EN e He)))). lia.
  - inversion ND as [| x l NINe NDr]; subst x l. clear ND. rename NDr into ND.
    assert (NIN : ~ In s rest) by (intros X; apply NINe; apply (proj2 (elem_of_In _ _)); exact X).
    destruct (COV s (or_introl eq_refl)) as [[u Hu]|HQ].
    + (* [comment removed for export] *)
      pose proof (as_livebytes_delete lm u _ Hu) as LB. cbn [li_n] in LB.
      assert (SZ : Z.of_nat (size lm) = 1 + Z.of_nat (size (delete u lm))).
      { rewrite (map_size_delete_Some u lm); [| rewrite Hu; eexists; reflexivity].
        destruct (size lm) eqn:SZ0; [| lia]. exfalso. apply map_size_empty_inv in SZ0. apply (f_equal (fun m => m !! u)) in SZ0. rewrite lookup_empty in SZ0. rewrite Hu in SZ0. discriminate. }
      destruct (IH (delete u lm) E ND) as [S1 S2].
      * intros u' li Hu'. rewrite lookup_delete_Some in Hu'. destruct Hu' as [_ Hu']. exact (LN u' li Hu').
      * exact EN.
      * intros s' Hs'. destruct (COV s' (or_intror Hs')) as [[u' Hu']|HQ']; [| right; exact HQ'].
        left. exists u'. rewrite lookup_delete_Some. split; [| exact Hu']. intros ->. rewrite Hu in Hu'. injection Hu' as E1 _. subst s'. exact (NIN Hs').
      * intros s' Hs'. exact (BIG s' (or_intror Hs')).
      * rewrite sec_n_sum_cons. cbn [length]. pose proof (BIG s (or_introl eq_refl)). lia.
    + (* [comment removed for export] *)
      apply in_map_iff in HQ as (e & He & HeE). (first [ pose proof ((in_split _ _ HeE)) as dR_1; dand3 dR_1 as E1 E2 -> | destruct (in_split _ _ HeE) as (E1 & E2 & ->) ]).
      destruct (EN e ltac:(apply in_app_iff; right; left; reflexivity)) as [E0 ECH].
      destruct s as [mb n0]. destruct (ECH mb n0 He) as [EQN EBIG]. cbn [cs_n] in *.
      destruct (IH lm (E1 ++ E2) ND LN) as [S1 S2].
      * intros e' He'. apply EN. apply in_app_iff in He' as [?|?]; apply in_app_iff; [left; assumption| right; right; assumption].
      * intros s' Hs'. destruct (COV s' (or_intror Hs')) as [L|HQ']; [left; exact L| right].
        apply in_map_iff in HQ' as (e' & He' & He'E). apply in_map_iff. exists e'. split; [exact He'|].
        apply in_app_iff in He'E as [X|[<-|X]]; [apply in_app_iff; left; exact X| | apply in_app_iff; right; exact X].
        exfalso. rewrite He in He'. injection He' as E1'. apply NIN. rewrite E1'. exact Hs'.
      * intros s' Hs'. exact (BIG s' (or_intror Hs')).
      * rewrite qsum_app in *. rewrite qsum_cons. rewrite sec_n_sum_cons. cbn [length cs_n].
        pose proof (BIG _ (or_introl eq_refl)) as B0. cbn [cs_n] in B0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NoDup_of_map : forall {A B} (f : A -> B) (l : list A), NoDup (map f l) -> NoDup l.
Proof.
  induction l as [|a l IH]; intros ND; [constructor|]. cbn in ND. inversion ND as [|x l' NI ND']; subst.
  constructor; [| exact (IH ND')]. intros X. apply NI. apply elem_of_In. apply in_map. apply elem_of_In. exact X.
Qed.

End CEIL.

Lemma q_entries_app : forall b1 b2, q_entries (b1 ++ b2) = q_entries b1 ++ q_entries b2.
Proof. intros. unfold q_entries. apply flat_map_app. Qed.

Lemma qsum_le_q_bytes : forall bs, (forall e, In e (q_entries bs) -> 0 <= qe_n e) -> qsum (q_entries bs) <= q_bytes bs.
Proof.
  induction bs as [|b bs IH]; intros H; [cbn; lia|].
  unfold q_entries. cbn [flat_map]. fold (q_entries bs). rewrite qsum_app.
  change (q_bytes (b :: bs)) with (batch_bytes b + q_bytes bs).
  assert (IHb : qsum (q_entries bs) <= q_bytes bs) by (apply IH; intros e He; apply H; unfold q_entries; cbn [flat_map]; apply in_app_iff; right; exact He).
  assert (B : qsum (ba_entries b) <= batch_bytes b).
  { unfold batch_bytes. assert (EB : forall e, In e (ba_entries b) -> 0 <= qe_n e) by (intros e He; apply H; unfold q_entries; cbn [flat_map]; apply in_app_iff; left; exact He).
    revert EB. generalize (ba_entries b) as l. induction l as [|e l IHl]; intros EB; [cbn; unfold kQuarantineBatchBytes; lia|].
    rewrite qsum_cons. cbn [fold_right]. pose proof (EB e (or_introl eq_refl)).
    assert (qe_n e <= qe_bytes e) by (unfold qe_bytes, user_size; destruct (Z.eqb_spec (qe_n e) 0); lia).
    specialize (IHl ltac:(intros; apply EB; right; assumption)). unfold kQuarantineBatchBytes in *. lia. }
  lia.
Qed.

Lemma map_size_le : forall n, 64512 < n < 2^32 -> map_size n <= n + 12296.
Proof.
  intros n Hn. unfold map_size, kPageSize. rewrite needed_size2_secondary by (unfold kMaxPrimaryUser; lia).
  pose proof (rounded_size_lt n). pose proof (round_up_lt (rounded_size n + 4096) 4096 ltac:(lia)). lia.
Qed.
Lemma map_size_ge : forall n, 64512 < n -> n + 4096 <= map_size n.
Proof.
  intros n Hn. unfold map_size, kPageSize. rewrite needed_size2_secondary by (unfold kMaxPrimaryUser; lia).
  pose proof (rounded_size_ge n). pose proof (round_up_ge (rounded_size n + 4096) 4096 ltac:(lia)). lia.
Qed.

Lemma sec_eager_le : forall ch, (forall s, In s ch -> 64512 < cs_n s < 2^32) ->
  sec_eager_ ch <= sec_n_sum ch + 12296 * Z.of_nat (length ch).
Proof.
  induction ch as [|s ch IH]; intros H; [cbn; lia|].
  change (sec_eager_ (s :: ch)) with (map_size (cs_n s) + sec_eager_ ch). rewrite sec_n_sum_cons. cbn [length].
  pose proof (map_size_le (cs_n s) (H s (or_introl eq_refl))). specialize (IH ltac:(intros; apply H; right; assumption)). lia.
Qed.

Section WFBounds.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variable A : AState.
  Hypothesis W : WF AL_pboth A.
  Local Notation ch := (sr_chunks (a_sec A)).

  Lemma wf_sec_sums :
    sec_n_sum ch <= LIVE_MAX + kQuarantineCacheSize + kQuarantineMaxSize /\
    Z.of_nat (length ch) <= NLIVE_MAX + 4178.
  Proof.
    (first [ pose proof ((wfS A W)) as dR_2; dand5 dR_2 as SND SLEN SRES SIN SCOV | destruct (wfS A W) as (SND & SLEN & SRES & SIN & SCOV) ]).
    (first [ pose proof ((wfV A W)) as dR_3; dand3 dR_3 as LV1 LV2 LV3 | destruct (wfV A W) as (LV1 & LV2 & LV3) ]).
    (first [ pose proof ((wfQ A W)) as dR_4; dand8 dR_4 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 | destruct (wfQ A W) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8) ]).
    (first [ pose proof ((wfB A W)) as dR_5; dand5 dR_5 as B1 B2 B3 B4 B5 | destruct (wfB A W) as (B1 & B2 & B3 & B4 & B5) ]).
    set (E := q_entries (a_qthread A ++ a_qglobal A)).
    assert (EN : forall e, In e E -> 0 <= qe_n e /\ (forall mb n0, qe_chunk e = ChS (CS mb n0) -> n0 = qe_n e /\ 64512 < qe_n e)).
    { intros e He. subst E. rewrite q_entries_app in He.
      assert (WE : wf_qentry_ (a_reg A) (a_sec A) e).
      { apply in_app_iff in He as [He|He]; unfold q_entries in He; apply in_flat_map in He as (b & Hb & Heb).
        - (first [ pose proof ((proj1 (Forall_forall _ _) Q1 b Hb)) as dR_6; dand3 dR_6 as _ _ WB | pose proof (proj1 (Forall_forall _ _) Q1 b Hb) as (_ & _ & WB) ]). exact (proj1 (Forall_forall _ _) WB e Heb).
        - (first [ pose proof ((proj1 (Forall_forall _ _) Q2 b Hb)) as dR_7; dand3 dR_7 as _ _ WB | pose proof (proj1 (Forall_forall _ _) Q2 b Hb) as (_ & _ & WB) ]). exact (proj1 (Forall_forall _ _) WB e Heb). }
      destruct WE as [R WE]. split; [lia|]. intros mb n0 Hc. rewrite Hc in WE. unfold kMaxPrimaryUser in WE. lia. }
    destruct (sec_sum_bound ch (a_livemap A) E) as [S1 S2].
    - exact (NoDup_of_map cs_map ch SND).
    - intros u li Hu. pose proof (LV1 u li Hu) as (X & _). lia.
    - exact EN.
    - intros s Hs. exact (SCOV s Hs).
    - intros s Hs. pose proof (SIN s Hs) as (X & _). unfold kMaxPrimaryUser in X. lia.
    - assert (QS : qsum E <= kQuarantineCacheSize + kQuarantineMaxSize).
      { subst E. rewrite q_entries_app, qsum_app.
        pose proof (qsum_le_q_bytes (a_qthread A) ltac:(intros e He; apply (proj1 (EN e ltac:(rewrite q_entries_app; apply in_app_iff; left; exact He))))).
        pose proof (qsum_le_q_bytes (a_qglobal A) ltac:(intros e He; apply (proj1 (EN e ltac:(rewrite q_entries_app; apply in_app_iff; right; exact He))))).
        lia. }
      unfold as_nlive_ in B3. rewrite NLIVE_MAX_eq in *. rewrite LIVE_MAX_eq in *. unfold kQuarantineCacheSize, kQuarantineMaxSize in *.
      split; [lia|]. nia.
  Qed.

  Lemma wf_sec_eager : sec_eager_ ch <= 2^32 /\ Z.of_nat (length ch) <= 8274.
  Proof.
    pose proof wf_sec_sums as [S1 S2]. (first [ pose proof ((wfS A W)) as dR_8; dand5 dR_8 as _ _ _ SIN _ | destruct (wfS A W) as (_ & _ & _ & SIN & _) ]).
    pose proof (sec_eager_le ch ltac:(intros s Hs; pose proof (SIN s Hs) as (X & _); unfold kMaxPrimaryUser, REQ_MAX in X; lia)) as SE.
    rewrite NLIVE_MAX_eq, LIVE_MAX_eq in *. unfold kQuarantineCacheSize, kQuarantineMaxSize in *. split; lia.
  Qed.
End WFBounds.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shadow_region_size : forall b s, 0 < s -> 0 <= snd (shadow_region b s) <= s / 8 + 16.
Proof.
  intros b s Hs. unfold shadow_region. cbn [snd].
  pose proof (round_down_le (sh b) 8 ltac:(lia)). pose proof (round_down_gt (sh b) 8 ltac:(lia)).
  pose proof (round_up_ge (sh (b + s - 1) + 1) 8 ltac:(lia)). pose proof (round_up_lt (sh (b + s - 1) + 1) 8 ltac:(lia)).
  assert (sh b <= sh (b + s - 1) <= sh b + s / 8 + 1).
  { unfold sh. pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
    pose proof (Z.div_mod (b + s - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + s - 1) 8 ltac:(lia)).
    pose proof (Z.div_mod s 8 ltac:(lia)). pose proof (Z.mod_pos_bound s 8 ltac:(lia)). nia. }
  lia.
Qed.

Lemma pa_image_ivs_bytes : hull_bytes pa_image_ivs = 6266880.   (* [comment removed for export] *)
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma fixed_regions_weight : forall P, 0 <= p_stk_span P <= 0x240000 ->
  (forall b s, In (b, s) (fixed_regions_ AL_pboth P) -> 0 <= s) /\
  regions_weight (fixed_regions_ AL_pboth P) <= 2^29.
Proof.
  intros P SP. pose proof alloc_ceiling_val as CE. unfold fixed_regions_. cbn [al_image_lo al_image_hi AL_pboth].
  unfold stack_shadow_iv, kFakeStackBytes, kDepotNodesBlock, kStackStoreBlockBytes, kChunksBlockCount.
  repeat match goal with |- context [shadow_region ?b ?s] =>
    pose proof (shadow_region_size b s ltac:(lia)); destruct (shadow_region b s) as [? ?] end.
  cbn [fst snd] in *. split.
  - intros b s Hin. cbn [In] in Hin.
    repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|] end. destruct Hin.
  - cbn [regions_weight fst snd app]. unfold page_size. lia.
Qed.

(* [comment removed for export] *)
Lemma lfixed_regions_weight : forall P, 0 <= p_stk_span P <= 0x240000 ->
  (forall b s, In (b, s) (lfixed_regions_ AL_pboth P) -> 0 <= s) /\
  regions_weight (lfixed_regions_ AL_pboth P) <= 2^29.
Proof.
  intros P SP. pose proof (fixed_regions_weight P SP) as [N W]. rewrite fixed_regions_split in N, W.
  cbn [regions_weight fst snd] in W. unfold page_size in W. split; [| lia].
  intros b s Hin. apply (N b s). right. exact Hin.
Qed.

End CEIL2.

(* [comment removed for export] *)
Fixpoint csize_sum_ (n : nat) : Z := match n with O => 0 | S n' => csize_sum_ n' + class_size (Z.of_nat n) end.
Fixpoint slack_sum_ (n : nat) : Z := match n with O => 0 | S n' => slack_sum_ n' + class_slack (Z.of_nat n) end.
Lemma csize_sum_30 : csize_sum_ 30 = 231936.
Proof. vm_compute. reflexivity. Qed.
Lemma slack_sum_30 : slack_sum_ 30 = kQuarantineMaxSize + kQuarantineCacheSize.
Proof. vm_compute. reflexivity. Qed.

Lemma class_eager_le : forall c R na, 1 <= c <= 30 -> 0 <= na -> wf_region c R na ->
  0 <= rg_mapped_user R /\ 0 <= rg_mapped_fa R /\
  8 * (rg_mapped_user R + rg_mapped_fa R) <= 9 * (class_size c * na) + 225 * class_size c + 6553600 + 9 * class_slack c.
Proof.
  intros c R na Hc Hna WR. pose proof (class_size_range c Hc) as CR. pose proof (class_slack_range c) as SL.
  (first [ dand12 WR as A1 _ _ A4 A5 _ _ _ _ _ A11 A12 | destruct WR as (A1 & _ & _ & A4 & A5 & _ & _ & _ & _ & _ & A11 & A12) ]).
  unfold kUserMapSize, kFreeArrayMapSize, kFreeArraySize, kMaxSize in *.
  set (au := rg_allocated_user R) in *. set (q := au / class_size c) in *.
  assert (Q : class_size c * q <= au) by (subst q; apply Z.mul_div_le; lia).
  assert (Q0 : 0 <= q) by (subst q; apply Z.div_pos; lia).
  split; [lia|]. split; [lia|]. nia.
Qed.

Lemma classes_eager_S : forall reg n,
  classes_eager_ reg (S n) = classes_eager_ reg n + rg_mapped_user (reg (Z.of_nat (S n))) + rg_mapped_fa (reg (Z.of_nat (S n))).
Proof. intros. reflexivity. Qed.
Lemma classes_eager_le : forall reg paid n, (n <= 30)%nat ->
  (forall c, 1 <= c <= Z.of_nat n -> wf_region c (reg c) (Z.of_nat (length (paid c)))) ->
  0 <= classes_eager_ reg n /\
  8 * classes_eager_ reg n <= 9 * paid_sum_ paid n + 225 * csize_sum_ n + 6553600 * Z.of_nat n + 9 * slack_sum_ n.
Proof.
  intros reg paid n. induction n as [|n IH]; intros Hn H; [cbn; lia|].
  cbn [classes_eager_ paid_sum_ csize_sum_ slack_sum_].
  destruct (IH ltac:(lia) ltac:(intros c Hc; apply H; lia)) as [P1 P2].
  pose proof (class_eager_le (Z.of_nat (S n)) (reg (Z.of_nat (S n))) (Z.of_nat (length (paid (Z.of_nat (S n))))) ltac:(lia) ltac:(lia) (H (Z.of_nat (S n)) ltac:(lia))) as (Q1 & Q2 & Q3).
  split; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Lemma lclass_regions_weight : forall sb R c,
  0 <= rg_mapped_user R -> 0 <= rg_mapped_fa R ->
  (forall b s, In (b, s) (lclass_regions_ sb R c) -> 0 <= s) /\
  8 * regions_weight (lclass_regions_ sb R c) <= rg_mapped_user R + rg_mapped_fa R + 131328.
Proof.
  intros sb R c MU FA. unfold lclass_regions_, page_size in *.
  destruct (Z.eqb_spec (rg_mapped_user R) 0) as [EU|EU]; destruct (Z.eqb_spec (rg_mapped_fa R) 0) as [EF|EF]; cbn [app];
  repeat match goal with |- context [shadow_region ?b ?s] =>
    pose proof (shadow_region_size b s ltac:(lia)); pose proof (Z.mul_div_le s 8 ltac:(lia)); destruct (shadow_region b s) as [? ?] end;
  cbn [fst snd regions_weight In] in *; unfold page_size;
  (split; [intros b s Hin; repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|] end; destruct Hin | lia]).
Qed.
Lemma lclasses_regions_weight : forall sb reg n,
  (forall c, 1 <= c <= Z.of_nat n -> 0 <= rg_mapped_user (reg c) /\ 0 <= rg_mapped_fa (reg c)) ->
  (forall b s, In (b, s) (lclasses_regions_ sb reg n) -> 0 <= s) /\
  8 * regions_weight (lclasses_regions_ sb reg n) <= classes_eager_ reg n + 131328 * Z.of_nat n.
Proof.
  induction n as [|n IH]; intros H.
  - cbn. split; [intros _ _ []| lia].
  - cbn [lclasses_regions_ classes_eager_]. rewrite regions_weight_app.
    destruct (IH ltac:(intros c Hc; apply H; lia)) as [P1 P2].
    destruct (H (Z.of_nat (S n)) ltac:(lia)) as [MU FA].
    destruct (lclass_regions_weight sb (reg (Z.of_nat (S n))) (Z.of_nat (S n)) MU FA) as [Q1 Q2].
    split; [| lia]. intros b s Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (P1 b s Hin)| exact (Q1 b s Hin)].
Qed.

Lemma sec_regions_weight : forall ch, (forall s, In s ch -> 64512 < cs_n s < 2^32) ->
  (forall b s, In (b, s) (sec_regions_ ch) -> 0 <= s) /\
  regions_weight (sec_regions_ ch) <= sec_eager_ ch + sec_eager_ ch / 8 + 16400 * Z.of_nat (length ch).
Proof.
  induction ch as [|c ch IH]; intros H.
  - cbn. split; [intros _ _ []| lia].
  - destruct (IH ltac:(intros; apply H; right; assumption)) as [P1 P2].
    pose proof (H c (or_introl eq_refl)) as Hc. pose proof (map_size_ge (cs_n c) ltac:(lia)) as MG.
    unfold sec_regions_ in *. cbn [flat_map app]. change (sec_eager_ (c :: ch)) with (map_size (cs_n c) + sec_eager_ ch).
    pose proof (shadow_region_size (cs_map c) (map_size (cs_n c)) ltac:(lia)) as SR.
    destruct (shadow_region (cs_map c) (map_size (cs_n c))) as [lo sz]. cbn [fst snd regions_weight length] in *.
    split.
    + intros b s [Hin|[Hin|Hin]]; [injection Hin as <- <-; lia| injection Hin as <- <-; lia| exact (P1 b s Hin)].
    + unfold page_size in *.
      assert (0 <= sec_eager_ ch).
      { clear - H. induction ch as [|c' ch IH']; [cbn; lia|]. change (sec_eager_ (c' :: ch)) with (map_size (cs_n c') + sec_eager_ ch).
        pose proof (map_size_ge (cs_n c') ltac:(pose proof (H c' ltac:(right; left; reflexivity)); lia)).
        specialize (IH' ltac:(intros; apply H; cbn [In] in *; tauto)). pose proof (H c' ltac:(right; left; reflexivity)). lia. }
      pose proof (Z.div_mod (map_size (cs_n c)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (map_size (cs_n c)) 8 ltac:(lia)).
      pose proof (Z.div_mod (sec_eager_ ch) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sec_eager_ ch) 8 ltac:(lia)).
      pose proof (Z.div_mod (map_size (cs_n c) + sec_eager_ ch) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (map_size (cs_n c) + sec_eager_ ch) 8 ltac:(lia)).
      nia.
Qed.

Lemma lsec_regions_weight : forall ch, (forall s, In s ch -> 64512 < cs_n s < 2^32) ->
  (forall b s, In (b, s) (lsec_regions_ ch) -> 0 <= s) /\
  regions_weight (lsec_regions_ ch) <= sec_eager_ ch / 8 + 16400 * Z.of_nat (length ch).
Proof.
  induction ch as [|c ch IH]; intros H.
  - cbn. split; [intros _ _ []| lia].
  - destruct (IH ltac:(intros; apply H; right; assumption)) as [P1 P2].
    pose proof (H c (or_introl eq_refl)) as Hc. pose proof (map_size_ge (cs_n c) ltac:(lia)) as MG.
    unfold lsec_regions_ in *. cbn [map]. change (sec_eager_ (c :: ch)) with (map_size (cs_n c) + sec_eager_ ch).
    pose proof (shadow_region_size (cs_map c) (map_size (cs_n c)) ltac:(lia)) as SR.
    destruct (shadow_region (cs_map c) (map_size (cs_n c))) as [lo sz]. cbn [fst snd regions_weight length] in *.
    split.
    + intros b s [Hin|Hin]; [injection Hin as <- <-; lia| exact (P1 b s Hin)].
    + unfold page_size in *.
      assert (0 <= sec_eager_ ch).
      { clear - H. induction ch as [|c' ch IH']; [cbn; lia|]. change (sec_eager_ (c' :: ch)) with (map_size (cs_n c') + sec_eager_ ch).
        pose proof (map_size_ge (cs_n c') ltac:(pose proof (H c' ltac:(right; left; reflexivity)); lia)).
        specialize (IH' ltac:(intros; apply H; cbn [In] in *; tauto)). pose proof (H c' ltac:(right; left; reflexivity)). lia. }
      pose proof (Z.div_mod (map_size (cs_n c)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (map_size (cs_n c)) 8 ltac:(lia)).
      pose proof (Z.div_mod (sec_eager_ ch) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sec_eager_ ch) 8 ltac:(lia)).
      pose proof (Z.div_mod (map_size (cs_n c) + sec_eager_ ch) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (map_size (cs_n c) + sec_eager_ ch) 8 ltac:(lia)).
      nia.
Qed.

(* [comment removed for export] *)
Definition kBudgetRoom : Z := 2^30 + 2^28.   (* [comment removed for export] *)

Section Room.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variable A : AState.
  Hypothesis W : WF AL_pboth A.
  Hypothesis X : wf_extra LPA pa_site_pcs (a_pl A).

  (* [comment removed for export] *)
  Lemma wf_class_nonneg : forall c, 1 <= c <= 31 -> 0 <= rg_mapped_user (a_reg A c) /\ 0 <= rg_mapped_fa (a_reg A c).
  Proof.
    intros c Hc. (first [ pose proof ((wfR A W)) as dR_9; dand3 dR_9 as R1 R2 _ | destruct (wfR A W) as (R1 & R2 & _) ]).
    destruct (Z.eq_dec c 31) as [->|NE].
    - rewrite (R2 31) by lia. cbn. lia.
    - destruct (R1 c ltac:(lia)) as (Q1 & _ & _ & _ & Q5 & _). lia.
  Qed.
  Lemma wf_classes_eager : 0 <= classes_eager_ (a_reg A) 31 /\ 8 * classes_eager_ (a_reg A) 31 <= 9 * PRIMCRED0 + 2674149888.
  Proof.
    (first [ pose proof ((wfR A W)) as dR_9; dand3 dR_9 as R1 R2 _ | destruct (wfR A W) as (R1 & R2 & _) ]).
    (first [ pose proof ((wfN A W)) as dR_8; dand3 dR_8 as N0 NS _ | destruct (wfN A W) as (N0 & NS & _) ]).
    pose proof (classes_eager_le (a_reg A) (a_paid A) 30 ltac:(lia) ltac:(intros c Hc; apply R1; lia)) as [P1 P2].
    rewrite csize_sum_30, slack_sum_30 in P2. unfold kQuarantineMaxSize, kQuarantineCacheSize in P2.
    rewrite (classes_eager_S (a_reg A) 30). rewrite (R2 (Z.of_nat 31)) by (clear; lia). cbn [rg_mapped_user rg_mapped_fa region_zero]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma wf_alregions_nonneg : forall b s, In (b, s) (alregions AL_pboth A) -> 0 <= s.
  Proof.
    intros b s Hin. unfold alregions, alregions_ in Hin.
    pose proof (wfP A W) as WP.
    assert (SP : 0 <= p_stk_span (a_pl A) <= 0x240000) by (apply wf_place_cheap in WP; lia).
    apply in_app_iff in Hin as [Hin|Hin]; [exact (proj1 (lfixed_regions_weight _ SP) b s Hin)|].
    apply in_app_iff in Hin as [Hin|Hin].
    - exact (proj1 (lclasses_regions_weight (p_sb (a_pl A)) (a_reg A) 31 ltac:(intros c Hc; apply wf_class_nonneg; lia)) b s Hin).
    - (first [ pose proof ((wfS A W)) as dR_11; dand5 dR_11 as _ _ _ SIN _ | destruct (wfS A W) as (_ & _ & _ & SIN & _) ]).
      exact (proj1 (lsec_regions_weight (sr_chunks (a_sec A)) ltac:(intros s' Hs'; pose proof (SIN s' Hs') as (Y & _); unfold kMaxPrimaryUser, REQ_MAX in Y; lia)) b s Hin).
  Qed.
  (* [comment removed for export] *)
  Lemma wf_lhull_bytes : 8 * hull_bytes (pa_lhull A) <=
    8 * (2^29 + (2^29 + 2^28) + 8192 * (400 * 1000) + (2^28 + 2^26)) + classes_eager_ (a_reg A) 31 + 131328 * 31.   (* [comment removed for export] *)
  Proof.
    unfold pa_lhull, alhull_of, alhull_of_, alregions_. rewrite !hull_bytes_app.
    pose proof (wfP A W) as WP.
    assert (SP : 0 <= p_stk_span (a_pl A) <= 0x240000) by (apply wf_place_cheap in WP; lia). clear WP.
    assert (HX : hull_bytes (p_extra (a_pl A)) <= 2^28 + 2^26) by (destruct X as (_ & _ & _ & _ & _ & HX & _); exact HX).
    assert (HD : hull_bytes (a_deadsh A) <= 8192 * (400 * 1000)).
    { (first [ pose proof ((wfE A W)) as dR_12; dand4 dR_12 as D1 _ _ D4 | destruct (wfE A W) as (D1 & _ & _ & D4) ]). unfold kDeadShadowBytes in D4. rewrite SECCRED0_eq in D1, D4.
      pose proof (Nat2Z.is_nonneg (length (sr_chunks (a_sec A)))). nia. }
    pose proof (hull_bytes_of_regions (alregions_ AL_pboth (a_pl A) (a_reg A) (a_sec A)) wf_alregions_nonneg) as HR.
    unfold alregions_ in HR. rewrite !regions_weight_app in HR.
    pose proof (proj2 (lfixed_regions_weight _ SP)) as F.
    pose proof (proj2 (lclasses_regions_weight (p_sb (a_pl A)) (a_reg A) 31 ltac:(intros c Hc; apply wf_class_nonneg; lia))) as C.
    (first [ pose proof ((wfS A W)) as dR_13; dand5 dR_13 as _ _ _ SIN _ | destruct (wfS A W) as (_ & _ & _ & SIN & _) ]).
    pose proof (proj2 (lsec_regions_weight (sr_chunks (a_sec A)) ltac:(intros s' Hs'; pose proof (SIN s' Hs') as (Y & _); unfold kMaxPrimaryUser, REQ_MAX in Y; lia))) as S.
    pose proof (wf_sec_eager A W) as [E1 E2].
    replace (Z.of_nat 31) with 31 in C by reflexivity.
    pose proof (Z.div_mod (sec_eager_ (sr_chunks (a_sec A))) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sec_eager_ (sr_chunks (a_sec A))) 8 ltac:(lia)).
    lia.
  Qed.

  Lemma wf_aeager : 0 <= aeager_of A /\ aeager_of A <= 2^25 + classes_eager_ (a_reg A) 31 + 2^17 + 2^32.   (* [comment removed for export] *)
  Proof.
    unfold aeager_of, aeager_of_.
    pose proof (wfP A W) as WP.
    assert (E0 : 0 <= p_eager0 (a_pl A) <= 2^25) by (apply wf_place_cheap in WP; lia). clear WP.
    pose proof wf_classes_eager as [C _].
    (first [ pose proof ((wfS A W)) as dR_14; dand5 dR_14 as _ SLEN SRES SIN _ | destruct (wfS A W) as (_ & SLEN & SRES & SIN & _) ]).
    pose proof (wf_sec_eager A W) as [E1 E2].
    assert (0 <= sec_eager_ (sr_chunks (a_sec A))).
    { generalize SIN. generalize (sr_chunks (a_sec A)) as ch. clear. induction ch as [|c ch IH]; intros H; [cbn; lia|].
      change (sec_eager_ (c :: ch)) with (map_size (cs_n c) + sec_eager_ ch).
      pose proof (H c (or_introl eq_refl)) as (Y & _). unfold kMaxPrimaryUser in Y. pose proof (map_size_ge (cs_n c) ltac:(lia)).
      specialize (IH ltac:(intros; apply H; right; assumption)). lia. }
    unfold kChunksBlockCount in SRES. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem wf_budget_room_min : aeager_of A + hull_bytes (pa_lhull A) + kBudgetRoom <= TLIM_MIN.   (* [comment removed for export] *)
  Proof. pose proof wf_lhull_bytes. pose proof wf_aeager. pose proof wf_classes_eager. unfold kBudgetRoom. rewrite TLIM_MIN_eq. rewrite PRIMCRED0_eq in *. lia. Qed.
  Lemma wf_extra_tlim : TLIM_MIN <= p_tlim (a_pl A).
  Proof. destruct X as (_ & _ & _ & _ & _ & _ & _ & T). exact T. Qed.
  Theorem wf_budget_room : aeager_of A + hull_bytes (pa_lhull A) + kBudgetRoom <= p_tlim (a_pl A).   (* [comment removed for export] *)
  Proof. pose proof wf_budget_room_min. pose proof wf_extra_tlim. lia. Qed.
End Room.

(* [comment removed for export] *)
Section CEIL3.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Corollary pa_budget_room {DR : DepotRep} : forall A m md, pa_ainv A m md ->
  aeager_of A + hull_bytes (pa_lhull A) + kBudgetRoom <= p_tlim (a_pl A).
Proof. intros A m md AI. exact (wf_budget_room A (ai_wf _ _ _ _ _ _ _ AI) (ai_extra _ _ _ _ _ _ _ AI)). Qed.

(* [comment removed for export] *)
Corollary pa_tlim_vm {DR : DepotRep} : forall A m md, pa_ainv A m md -> vm_limit (m_vmmaps md) = p_tlim (a_pl A).
Proof. intros A m md AI. destruct (ai_ledger _ _ _ _ _ _ _ AI) as (_ & _ & _ & _ & L5 & _). exact L5. Qed.
Corollary pa_budget_room_vm {DR : DepotRep} : forall A m md, pa_ainv A m md ->
  aeager_of A + hull_bytes (pa_lhull A) + kBudgetRoom <= vm_limit (m_vmmaps md).
Proof. intros A m md AI. rewrite (pa_tlim_vm A m md AI). exact (pa_budget_room A m md AI). Qed.

End CEIL3.
