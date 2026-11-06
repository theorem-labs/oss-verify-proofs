(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module AQWfJ.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AInv ABudget.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lcredit_cons : forall b bs, lcredit (b :: bs) = bcredit b + lcredit bs. Proof. reflexivity. Qed.
Lemma lcredit_nil : lcredit [] = 0. Proof. reflexivity. Qed.
Lemma lcredit_app : forall l1 l2, lcredit (l1 ++ l2) = lcredit l1 + lcredit l2.
Proof. intros l1 l2. induction l1 as [|b l1 IH]; [reflexivity|]. change ((b :: l1) ++ l2) with (b :: (l1 ++ l2)). rewrite !lcredit_cons, IH. lia. Qed.
Lemma lcredit_eq : forall bs, lcredit bs = q_bytes bs - 16384 * Z.of_nat (length bs).
Proof. intros bs. induction bs as [|b bs IH]; [reflexivity|]. rewrite lcredit_cons, q_bytes_cons. cbn [length]. unfold bcredit. lia. Qed.

Definition ntiny (es : list qentry) : Z := Z.of_nat (length (filter (fun e => Z.ltb (qe_n e) 16) es)).
Lemma ntiny_cons : forall e es, ntiny (e :: es) = (if Z.ltb (qe_n e) 16 then 1 else 0) + ntiny es.
Proof. intros e es. unfold ntiny. change (e :: es) with ([e] ++ es). rewrite filter_app', length_app, filter_tiny_single. destruct (qe_n e <? 16); lia. Qed.
Lemma ntiny_app : forall l1 l2, ntiny (l1 ++ l2) = ntiny l1 + ntiny l2.
Proof. intros. unfold ntiny. rewrite filter_app', length_app. lia. Qed.
Lemma ntiny_nonneg : forall es, 0 <= ntiny es. Proof. intros. unfold ntiny. apply Nat2Z.is_nonneg. Qed.
Lemma ntiny_nil : ntiny [] = 0. Proof. reflexivity. Qed.
Lemma ntiny_le_len : forall es, ntiny es <= Z.of_nat (length es).
Proof. intros es. induction es as [|e es IH]; [rewrite ntiny_nil; cbn; lia|]. rewrite ntiny_cons. cbn [length]. rewrite Nat2Z.inj_succ. destruct (qe_n e <? 16); lia. Qed.

(* [comment removed for export] *)
Lemma ebytes_lower : forall `{Clg : Ceiling} reg sec es, Forall (wf_qentry_ reg sec) es -> 16 * Z.of_nat (length es) - 15 * ntiny es <= ebytes es.
Proof.
  intros Clg reg sec es F. induction es as [|e es IH]; [rewrite ntiny_nil; cbn; lia|].
  rewrite ebytes_cons, ntiny_cons. cbn [length]. rewrite Nat2Z.inj_succ.
  inversion F as [|x l WE F']; subst. specialize (IH F'). destruct WE as [NR _].
  unfold qe_bytes. pose proof (user_size_pos (qe_n e) ltac:(lia)) as (U1 & U2 & U3).
  destruct (Z.ltb_spec (qe_n e) 16); lia.
Qed.
Lemma ebytes_nonneg : forall `{Clg : Ceiling} reg sec es, Forall (wf_qentry_ reg sec) es -> 0 <= ebytes es.
Proof. intros Clg reg sec es F. pose proof (ebytes_lower reg sec es F). pose proof (ntiny_le_len es). lia. Qed.

(* [comment removed for export] *)
Lemma lcredit_full : forall `{Clg : Ceiling} reg sec bs,
  Forall (wf_batch_ reg sec) bs -> (forall b, In b bs -> Z.of_nat (length (ba_entries b)) = kQuarantineBatchCount) ->
  8144 * Z.of_nat (length bs) - 15 * ntiny (q_entries bs) <= lcredit bs.
Proof.
  intros Clg reg sec bs F FULL. induction bs as [|b bs IH]; [rewrite lcredit_nil; cbn [q_entries flat_map length]; rewrite ntiny_nil; lia|].
  rewrite lcredit_cons, q_entries_cons, ntiny_app. cbn [length]. rewrite Nat2Z.inj_succ.
  inversion F as [|x l WB F']; subst. specialize (IH F' ltac:(intros b' H; apply FULL; right; exact H)).
  destruct WB as (_ & _ & FE). pose proof (ebytes_lower reg sec _ FE) as EL. rewrite (FULL b ltac:(left; reflexivity)) in EL.
  unfold bcredit. rewrite batch_bytes_ebytes. unfold kQuarantineBatchBytes, kQuarantineBatchCount in *. lia.
Qed.
(* [comment removed for export] *)
Lemma bcredit_lower : forall `{Clg : Ceiling} reg sec b, wf_batch_ reg sec b -> -8192 <= bcredit b.
Proof. intros Clg reg sec b (_ & _ & FE). unfold bcredit. rewrite batch_bytes_ebytes. pose proof (ebytes_nonneg reg sec _ FE). unfold kQuarantineBatchBytes. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lcredit_thread_suffix : forall `{Clg : Ceiling} reg sec qt i,
  Forall (wf_batch_ reg sec) qt -> (forall b, In b (removelast qt) -> Z.of_nat (length (ba_entries b)) = kQuarantineBatchCount) ->
  ntiny (q_entries qt) <= TINYCRED0 ->
  -8192 <= lcredit (skipn i qt).
Proof.
  intros Clg reg sec qt i F FULL NT.
  destruct qt as [|b0 r] eqn:E; [rewrite skipn_nil; cbn; lia|]. rewrite <- E in *.
  assert (NE : qt <> []) by (rewrite E; discriminate).
  pose proof (removelast_last_app qt (BA 0 []) NE) as SPL. set (l := removelast qt) in *. set (bl := last qt (BA 0 [])) in *.
  rewrite <- SPL in F |- *. rewrite skipn_app. apply Forall_app in F as [Fl Fb]. pose proof (Forall_inv Fb) as WB.
  rewrite lcredit_app. pose proof (bcredit_lower reg sec bl WB) as BL.
  assert (FS : forall b, In b (skipn i l) -> Z.of_nat (length (ba_entries b)) = kQuarantineBatchCount).
  { intros b Hb. apply FULL. rewrite <- (firstn_skipn i l). apply in_or_app. right. exact Hb. }
  assert (Fs : Forall (wf_batch_ reg sec) (skipn i l)).
  { apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) Fl). rewrite <- (firstn_skipn i l). apply in_or_app. right. exact Hb. }
  pose proof (lcredit_full reg sec (skipn i l) Fs FS) as CF.
  assert (NTs : ntiny (q_entries (skipn i l)) <= TINYCRED0).
  { rewrite <- SPL, <- (firstn_skipn i l), <- app_assoc, !q_entries_app, !ntiny_app in NT.
    pose proof (ntiny_nonneg (q_entries (firstn i l))). pose proof (ntiny_nonneg (q_entries [bl])). lia. }
  rewrite TINYCRED0_eq in NTs.
  assert (CL : 0 <= lcredit (skipn i l)).
  { pose proof (ntiny_nonneg (q_entries (skipn i l))) as NN0. destruct (skipn i l) as [|b1 bs1]; [rewrite lcredit_nil; lia|].
    cbn [length] in CF. rewrite Nat2Z.inj_succ in CF. pose proof (Nat2Z.is_nonneg (length bs1)). lia. }
  destruct (i - length l)%nat as [|k].
  - cbn [skipn]. rewrite lcredit_cons, lcredit_nil. lia.
  - cbn [skipn]. rewrite skipn_nil, lcredit_nil. lia.
Qed.

(* [comment removed for export] *)
Lemma lcredit_thread_drained : forall `{Clg : Ceiling} reg sec qt,
  Forall (wf_batch_ reg sec) qt -> (forall b, In b (removelast qt) -> Z.of_nat (length (ba_entries b)) = kQuarantineBatchCount) ->
  ntiny (q_entries qt) <= TINYCRED0 -> kQuarantineCacheSize < q_bytes qt ->
  16384 <= lcredit qt.
Proof.
  intros Clg reg sec qt F FULL NT SZ. unfold kQuarantineCacheSize in *. rewrite TINYCRED0_eq in NT.
  destruct (Z.le_gt_cases (Z.of_nat (length qt)) 63) as [SMALL|BIG].
  - rewrite lcredit_eq. lia.
  - assert (NE : qt <> []) by (intros ->; cbn in BIG; lia).
    pose proof (removelast_last_app qt (BA 0 []) NE) as SPL. set (l := removelast qt) in *. set (bl := last qt (BA 0 [])) in *.
    rewrite <- SPL in F, NT, BIG |- *. apply Forall_app in F as [Fl Fb]. pose proof (Forall_inv Fb) as WB.
    rewrite lcredit_app, lcredit_cons, lcredit_nil. rewrite q_entries_app, ntiny_app in NT.
    pose proof (lcredit_full reg sec l Fl FULL) as CF. pose proof (bcredit_lower reg sec bl WB) as BL.
    rewrite length_app in BIG. cbn [length] in BIG.
    pose proof (ntiny_nonneg (q_entries [bl])). pose proof (ntiny_nonneg (q_entries l)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section QCredit.
  Context {Clg : Ceiling}.
  Variables (reg : Z -> region) (lm : gmap Z liveinfo) (qt qg : list batch) (sec : secreg) (tiny B : Z).
  Hypothesis WQ : wf_quarantineB B reg lm qt qg sec.
  Hypothesis WB : wf_budget_ tiny lm qt qg.
  Hypothesis WJ : wf_qcredit_ qg.

  Lemma thread_ntiny : ntiny (q_entries qt) <= TINYCRED0.
  Proof.
    destruct WB as (T0 & _ & _ & TL & TB). unfold tiny_quar_ in TB. rewrite q_entries_app in TB. fold (ntiny (q_entries qt ++ q_entries qg)) in TB.
    rewrite ntiny_app in TB. pose proof (ntiny_nonneg (q_entries qg)). lia.
  Qed.

  Theorem wf_qcredit_transfer : kQuarantineCacheSize < q_bytes qt -> wf_qcredit_ (qtransfer qt qg).
  Proof.
    intros SZ. destruct WQ as (Q1 & Q2 & Q3 & _). destruct WJ as [J1 J2]. unfold qtransfer. pose proof thread_ntiny as NT.
    pose proof (lcredit_thread_drained reg sec qt Q1 Q3 NT SZ) as CD.
    split.
    - intros i. rewrite skipn_app, lcredit_app.
      destruct (Nat.le_gt_cases (length qg) i) as [GE|LT].
      + rewrite skipn_all2 by exact GE. rewrite lcredit_nil. exact (lcredit_thread_suffix reg sec qt _ Q1 Q3 NT).
      + replace (i - length qg)%nat with 0%nat by lia. rewrite skipn_O. specialize (J1 i). lia.
    - right. rewrite lcredit_app. specialize (J1 0%nat). rewrite skipn_O in J1. lia.
  Qed.

  Theorem wf_qcredit_rsplit : forall min, 0 <= min <= kQuarantineMinSize -> let (R, rest) := rsplit qg min in wf_qcredit_ rest.
  Proof.
    intros min Hmin. pose proof (rsplit_app qg min) as APP. pose proof (rsplit_rest_small qg min ltac:(lia)) as SM.
    destruct (rsplit qg min) as [R rest]. destruct WJ as [J1 J2]. split.
    - intros i. specialize (J1 (length R + i)%nat). rewrite APP, skipn_app, skipn_all2 in J1 by lia.
      replace (length R + i - length R)%nat with i in J1 by lia. exact J1.
    - left. destruct SM as [SM| ->]; [lia| cbn; unfold kQuarantineMinSize; lia].
  Qed.

  (* [comment removed for export] *)
  Theorem wf_qcredit_nomerge : kQuarantineMinSize < q_bytes qg -> 16384 * Z.of_nat (length qg) <= q_bytes qg.
  Proof. intros GT. destruct WJ as [J1 [J2|J2]]; [lia|]. rewrite lcredit_eq in J2. lia. Qed.
End QCredit.
End AQWfJ.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Inductive pstate := PF | PC | PV | PQ | PB.
Definition pstate_eq_dec : forall x y : pstate, {x = y} + {x <> y}. Proof. decide equality. Defined.

(* [comment removed for export] *)
Record ptuple := PT { pt_reg : Z -> region; pt_cache : Z -> pcache; pt_lm : gmap Z liveinfo; pt_qt : list batch; pt_qg : list batch }.

Definition pholds (T : ptuple) (c k : Z) (s : pstate) : Prop :=
  match s with
  | PF => p_free_ (pt_reg T) c k
  | PC => p_cached_ (pt_cache T) c k
  | PV => p_live_ (pt_lm T) c k
  | PQ => p_quar_ (pt_qt T) (pt_qg T) c k
  | PB => p_batch_ (pt_qt T) (pt_qg T) c k
  end.

Definition wf_partition_T (T : ptuple) : Prop := wf_partition_ (pt_reg T) (pt_cache T) (pt_lm T) (pt_qt T) (pt_qg T).

(* [comment removed for export] *)
Definition pfun (T : ptuple) : Prop :=
  forall c k, 1 <= c <= 30 -> 0 <= k < carved_count_ (pt_reg T) c ->
    (exists s, pholds T c k s) /\ (forall s s', pholds T c k s -> pholds T c k s' -> s = s').

Lemma wf_partition_pfun : forall T, wf_partition_T T <-> pfun T.
Proof.
  intros T. unfold wf_partition_T, wf_partition_, pfun. split.
  - intros W c k Hc Hk. specialize (W c k Hc Hk). cbv zeta in W.
    (first [ dand11 W as EX N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 | destruct W as (EX & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10) ]). split.
    + destruct EX as [H|[H|[H|[H|H]]]]; [exists PF|exists PC|exists PV|exists PQ|exists PB]; exact H.
    + intros s s' Hs Hs'. destruct s, s'; cbn [pholds] in Hs, Hs'; try reflexivity; exfalso; tauto.
  - intros P c k Hc Hk. specialize (P c k Hc Hk). destruct P as [[s Hs] U]. cbv zeta.
    split; [destruct s; cbn [pholds] in Hs; tauto|].
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros [H1 H2];
      match goal with
      | H1 : ?A, H2 : ?B |- False =>
          first [ discriminate (U PF PC H1 H2) | discriminate (U PF PV H1 H2) | discriminate (U PF PQ H1 H2) | discriminate (U PF PB H1 H2)
                | discriminate (U PC PV H1 H2) | discriminate (U PC PQ H1 H2) | discriminate (U PC PB H1 H2)
                | discriminate (U PV PQ H1 H2) | discriminate (U PV PB H1 H2) | discriminate (U PQ PB H1 H2) ]
      end.
Qed.

(* [comment removed for export] *)
Lemma partition_move : forall (T T' : ptuple) (c0 k0 : Z) (X Y : pstate),
  pfun T ->
  (forall c, carved_count_ (pt_reg T') c = carved_count_ (pt_reg T) c) ->
  1 <= c0 <= 30 -> 0 <= k0 < carved_count_ (pt_reg T) c0 ->
  pholds T c0 k0 X ->
  (forall s, pholds T' c0 k0 s <-> (s = Y \/ (s <> X /\ pholds T c0 k0 s))) ->
  (forall c k s, 1 <= c <= 30 -> 0 <= k < carved_count_ (pt_reg T) c -> (c, k) <> (c0, k0) -> (pholds T' c k s <-> pholds T c k s)) ->
  pfun T'.
Proof.
  intros T T' c0 k0 X Y P CC Hc0 Hk0 HX MV OTH c k Hc Hk. rewrite CC in Hk.
  destruct (P c k Hc Hk) as [[s Hs] U].
  destruct (Z.eq_dec c c0) as [->|NC]; [destruct (Z.eq_dec k k0) as [->|NK]|].
  - (* [comment removed for export] *) split.
    + exists Y. apply MV. left. reflexivity.
    + intros s1 s2 H1 H2. apply MV in H1. apply MV in H2.
      destruct H1 as [->|[N1 H1]]; destruct H2 as [->|[N2 H2]]; try reflexivity.
      * exfalso. apply N2. exact (U _ _ H2 HX).
      * exfalso. apply N1. exact (U _ _ H1 HX).
      * exact (U _ _ H1 H2).
  - assert (NE : (c0, k) <> (c0, k0)) by congruence.
    split; [exists s; apply (OTH _ _ _ Hc Hk NE); exact Hs|].
    intros s1 s2 H1 H2. apply (OTH _ _ _ Hc Hk NE) in H1. apply (OTH _ _ _ Hc Hk NE) in H2. exact (U _ _ H1 H2).
  - assert (NE : (c, k) <> (c0, k0)) by congruence.
    split; [exists s; apply (OTH _ _ _ Hc Hk NE); exact Hs|].
    intros s1 s2 H1 H2. apply (OTH _ _ _ Hc Hk NE) in H1. apply (OTH _ _ _ Hc Hk NE) in H2. exact (U _ _ H1 H2).
Qed.

(* [comment removed for export] *)
Lemma partition_same : forall (T T' : ptuple),
  pfun T ->
  (forall c, carved_count_ (pt_reg T') c = carved_count_ (pt_reg T) c) ->
  (forall c k s, 1 <= c <= 30 -> 0 <= k < carved_count_ (pt_reg T) c -> (pholds T' c k s <-> pholds T c k s)) ->
  pfun T'.
Proof.
  intros T T' P CC OTH c k Hc Hk. rewrite CC in Hk. destruct (P c k Hc Hk) as [[s Hs] U].
  split; [exists s; apply (OTH _ _ _ Hc Hk); exact Hs|].
  intros s1 s2 H1 H2. apply (OTH _ _ _ Hc Hk) in H1. apply (OTH _ _ _ Hc Hk) in H2. exact (U _ _ H1 H2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.
Local Open Scope Z_scope.

Section LiveDelete.
  Variables (lm : gmap Z liveinfo) (u : Z) (li : liveinfo).
  Hypothesis LU : lm !! u = Some li.
  (* [comment removed for export] *)
  Hypothesis UNIQ : forall u' li', lm !! u' = Some li' -> u <> u' -> li_chunk li <> li_chunk li'.

  Lemma p_live_delete_other : forall c k, li_chunk li <> ChP (CP c k) -> (p_live_ (delete u lm) c k <-> p_live_ lm c k).
  Proof.
    intros c k NEQ. unfold p_live_. split.
    - ((first [ intro dR_8; dex2 dR_8 as u0 n0; rename dR_8 into H | intro dR_8; dand3 dR_8 as u0 n0 H | intros (u0 & n0 & H) ])). rewrite lookup_delete_Some in H. destruct H as [_ H]. exists u0, n0. exact H.
    - ((first [ intro dR_9; dex2 dR_9 as u0 n0; rename dR_9 into H | intro dR_9; dand3 dR_9 as u0 n0 H | intros (u0 & n0 & H) ])). exists u0, n0. rewrite lookup_delete_Some. split; [| exact H].
      intros ->. rewrite LU in H. injection H as E. apply NEQ. rewrite E. reflexivity.
  Qed.
  Lemma p_live_delete_self : forall c k, li_chunk li = ChP (CP c k) -> ~ p_live_ (delete u lm) c k.
  Proof.
    (intros c k E; (first [ intro dR_10; dex2 dR_10 as u0 n0; rename dR_10 into H | intro dR_10; dand3 dR_10 as u0 n0 H | intros (u0 & n0 & H) ])). rewrite lookup_delete_Some in H. destruct H as [NEu H].
    apply (UNIQ u0 _ H); [congruence|]. cbn [li_chunk]. exact E.
  Qed.
End LiveDelete.

Section QuarPush.
  Variables (qt qg : list batch) (e : qentry).

  Lemma p_quar_push_last : qt <> [] -> forall c k,
    p_quar_ (qpush_last qt e) qg c k <-> p_quar_ qt qg c k \/ qe_chunk e = ChP (CP c k).
  Proof.
    intros NE c k. unfold p_quar_. rewrite !q_entries_app, (qpush_last_entries qt e NE). split.
    - intros (n & H). rewrite !in_app_iff in H. cbn [In] in H. destruct H as [[H|[H|[]]]|H].
      + left. exists n. apply in_app_iff. left. exact H.
      + right. rewrite H. reflexivity.
      + left. exists n. apply in_app_iff. right. exact H.
    - intros [(n & H)|E].
      + exists n. rewrite in_app_iff in H. rewrite !in_app_iff. cbn [In]. tauto.
      + exists (qe_n e). rewrite !in_app_iff. cbn [In]. left. right. left. destruct e as [ch n]; cbn in E |- *. rewrite E. reflexivity.
  Qed.
  Lemma p_batch_push_last : qt <> [] -> forall c k, p_batch_ (qpush_last qt e) qg c k <-> p_batch_ qt qg c k.
  Proof. intros NE c k. unfold p_batch_. rewrite (batch_indices_push_last qt qg e NE). tauto. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End QuarPush.

Section Transfer.
  Variables (qt qg : list batch).
  Lemma p_quar_transfer : forall c k, p_quar_ [] (qtransfer qt qg) c k <-> p_quar_ qt qg c k.
  Proof.
    intros c k. unfold p_quar_. rewrite !q_entries_app. split; intros (n & H); exists n.
    - apply (proj1 (q_entries_transfer_perm qt qg _)). exact H.
    - apply (proj2 (q_entries_transfer_perm qt qg _)). exact H.
  Qed.
  Lemma p_batch_transfer : forall c k, p_batch_ [] (qtransfer qt qg) c k <-> p_batch_ qt qg c k.
  Proof. intros c k. unfold p_batch_. rewrite (batch_indices_transfer qt qg). tauto. Qed.
End Transfer.

Section CacheReg.
  Variables (reg : Z -> region) (cache : Z -> pcache).

  Lemma p_cached_set : forall c ks c' k,
    p_cached_ (cache_set cache c ks) c' k <-> ((c' = c /\ In k ks) \/ (c' <> c /\ p_cached_ cache c' k)).
  Proof.
    intros c ks c' k. unfold p_cached_, cache_set. destruct (Z.eqb_spec c' c) as [->|NE]; cbn [pk_chunks].
    - split; [intros H; left; auto | intros [[_ H]|[H _]]; [exact H| congruence]].
    - split; [intros H; right; auto | intros [[H _]|[_ H]]; [congruence| exact H]].
  Qed.

  Lemma p_free_set : forall c R c' k,
    p_free_ (reg_set reg c R) c' k <-> ((c' = c /\ In k (rg_free R)) \/ (c' <> c /\ p_free_ reg c' k)).
  Proof.
    intros c R c' k. unfold p_free_, reg_set. destruct (Z.eqb_spec c' c) as [->|NE].
    - split; [intros H; left; auto | intros [[_ H]|[H _]]; [exact H| congruence]].
    - split; [intros H; right; auto | intros [[H _]|[_ H]]; [congruence| exact H]].
  Qed.

  Lemma carved_count_reg_set : forall c R c', rg_allocated_user R = rg_allocated_user (reg c) ->
    carved_count_ (reg_set reg c R) c' = carved_count_ reg c'.
  Proof.
    intros c R c' E. unfold carved_count_, reg_set. destruct (Z.eqb_spec c' c) as [->|NE]; [rewrite E|]; reflexivity.
  Qed.
  Lemma reg_return_allocated : forall R out fa', rg_allocated_user (reg_return R out fa') = rg_allocated_user R.
  Proof. reflexivity. Qed.
  Lemma reg_return_free : forall R out fa', rg_free (reg_return R out fa') = rg_free R ++ out.
  Proof. reflexivity. Qed.
  Lemma reg_return_mapped_user : forall R out fa', rg_mapped_user (reg_return R out fa') = rg_mapped_user R.
  Proof. reflexivity. Qed.
  Lemma reg_return_mapped_fa : forall R out fa', rg_mapped_fa (reg_return R out fa') = fa'.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma wf_caches_set : forall ci c ks,
    wf_caches_ reg cache ci -> 1 <= c <= 30 ->
    Z.of_nat (length ks) <= max_count c -> NoDup ks -> (forall k, In k ks -> 0 <= k < carved_count_ reg c) -> (ci = false -> ks = []) ->
    wf_caches_ reg (cache_set cache c ks) ci.
  Proof.
    (intros ci c ks; (first [ intro dR_11; dand3 dR_11 as W1 W31 W0 | intros (W1 & W31 & W0) ]); intros Hc L ND RG CI). unfold wf_caches_, cache_set.
    split; [| split; [destruct (Z.eqb_spec 31 c); [lia| exact W31] | destruct (Z.eqb_spec 0 c); [lia| exact W0]]].
    intros c' Hc'. destruct (Z.eqb_spec c' c) as [->|NE]; cbn [pk_chunks]; [| exact (W1 c' Hc')].
    cbv zeta. split; [exact L|]. split; [exact ND|]. split; [exact RG| exact CI].
  Qed.
End CacheReg.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RecPrim.
  Variables (reg : Z -> region) (cache : Z -> pcache) (c k : Z) (fa' : Z).
  Let ks := pk_chunks (cache c).
  Let pr := cache_push_list ks (max_count c) k.
  Definition recp_cache : Z -> pcache := cache_set cache c (fst pr).
  Definition recp_reg : Z -> region :=
    if Z.of_nat (length ks) =? max_count c then reg_set reg c (reg_return (reg c) (snd pr) fa') else reg.

  Lemma recp_out_nil : Z.of_nat (length ks) <> max_count c -> snd pr = [].
  Proof. intros NE. subst pr. unfold cache_push_list. destruct (Z.eqb_spec (Z.of_nat (length ks)) (max_count c)); [lia| reflexivity]. Qed.

  Lemma recp_carved : forall c', carved_count_ recp_reg c' = carved_count_ reg c'.
  Proof.
    intros c'. unfold recp_reg. destruct (Z.of_nat (length ks) =? max_count c); [| reflexivity].
    apply carved_count_reg_set. reflexivity.
  Qed.

  Lemma p_cached_recp : forall c' k',
    p_cached_ recp_cache c' k' <-> ((c' = c /\ In k' (fst pr)) \/ (c' <> c /\ p_cached_ cache c' k')).
  Proof. intros. unfold recp_cache. apply p_cached_set. Qed.

  Lemma p_free_recp : forall c' k',
    p_free_ recp_reg c' k' <-> (p_free_ reg c' k' \/ (c' = c /\ In k' (snd pr))).
  Proof.
    intros c' k'. unfold recp_reg. destruct (Z.eqb_spec (Z.of_nat (length ks)) (max_count c)) as [E|NE].
    - rewrite p_free_set. rewrite reg_return_free, in_app_iff. unfold p_free_.
      destruct (Z.eq_dec c' c) as [->|NC]; tauto.
    - rewrite (recp_out_nil NE). cbn [In]. tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma recp_in : forall x, (In x (fst pr) \/ In x (snd pr)) <-> (In x ks \/ x = k).
  Proof. intros x. subst pr. apply cache_push_list_in. Qed.
  Lemma recp_disjoint : NoDup ks -> ~ In k ks -> forall x, In x (fst pr) -> ~ In x (snd pr).
  Proof.
    intros ND NK x H1 H2. subst pr. unfold cache_push_list in H1, H2.
    destruct (Z.of_nat (length ks) =? max_count c); cbn [fst snd] in H1, H2; [| destruct H2].
    apply in_app_iff in H1 as [H1|[<-|[]]].
    - (first [ pose proof ((drain_nodup ks (Z.to_nat (max_count c / 2)) ND)) as dR_2; dand3 dR_2 as _ _ DJ | destruct (drain_nodup ks (Z.to_nat (max_count c / 2)) ND) as (_ & _ & DJ) ]). exact (DJ x H1 H2).
    - apply NK. apply (drain_in_iff ks (Z.to_nat (max_count c / 2))). right. exact H2.
  Qed.
  Lemma recp_nodup : NoDup ks -> ~ In k ks -> NoDup (fst pr) /\ NoDup (snd pr).
  Proof.
    intros ND NK. subst pr. unfold cache_push_list.
    destruct (Z.of_nat (length ks) =? max_count c); cbn [fst snd].
    - (first [ pose proof ((drain_nodup ks (Z.to_nat (max_count c / 2)) ND)) as dR_3; dand3 dR_3 as N1 N2 DJ | destruct (drain_nodup ks (Z.to_nat (max_count c / 2)) ND) as (N1 & N2 & DJ) ]). split; [| exact N2].
      apply NoDup_snoc; [exact N1|]. intros H. apply NK. apply (drain_in_iff ks (Z.to_nat (max_count c / 2))). left. exact H.
    - split; [apply NoDup_snoc; [exact ND| exact NK] | constructor].
  Qed.
  (* [comment removed for export] *)
End RecPrim.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FreePartition.
  Variables (reg : Z -> region) (cache : Z -> pcache) (lm : gmap Z liveinfo) (qt qg : list batch) (u : Z) (li : liveinfo).
  Hypothesis P : pfun (PT reg cache lm qt qg).
  Hypothesis LU : lm !! u = Some li.
  Hypothesis UNIQ : forall u' li', lm !! u' = Some li' -> u <> u' -> li_chunk li <> li_chunk li'.
  (* [comment removed for export] *)
  Hypothesis LRANGE : forall c k, li_chunk li = ChP (CP c k) -> 1 <= c <= 30 /\ 0 <= k < carved_count_ reg c.
  Let e := QE (li_chunk li) (li_n li).

  (* [comment removed for export] *)
  Lemma pfun_free_gen : forall qt',
    (forall c k, p_quar_ qt' qg c k <-> p_quar_ qt qg c k \/ qe_chunk e = ChP (CP c k)) ->
    (forall c k, p_batch_ qt' qg c k <-> p_batch_ qt qg c k) ->
    pfun (PT reg cache (delete u lm) qt' qg).
  Proof.
    intros qt' HQ HB. destruct (li_chunk li) as [[c0 k0]|s] eqn:ECH; rewrite <- ECH in UNIQ; try rewrite <- ECH in LRANGE.
    - (* [comment removed for export] *)
      destruct (LRANGE c0 k0 ECH) as [Hc0 Hk0].
      apply (partition_move (PT reg cache lm qt qg) _ c0 k0 PV PQ P); cbn [pt_reg pt_cache pt_lm pt_qt pt_qg].
      + intros; reflexivity.
      + exact Hc0.
      + exact Hk0.
      + exists u, (li_n li). cbn [pt_lm]. rewrite LU. destruct li as [ch n]; cbn in ECH |- *. rewrite ECH. reflexivity.
      + intros s. destruct s; cbn [pholds pt_reg pt_cache pt_lm pt_qt pt_qg].
        * split; [intros H; right; split; [discriminate| exact H] | intros [H|[_ H]]; [discriminate| exact H]].
        * split; [intros H; right; split; [discriminate| exact H] | intros [H|[_ H]]; [discriminate| exact H]].
        * split; [intros H; exfalso; exact (p_live_delete_self lm u li UNIQ c0 k0 ECH H) | intros [H|[H _]]; [discriminate| congruence]].
        * split; [intros _; left; reflexivity | intros _; apply HQ; right; unfold e; cbn [qe_chunk]; reflexivity].
        * rewrite HB. split; [intros H; right; split; [discriminate| exact H] | intros [H|[_ H]]; [discriminate| exact H]].
      + intros c k s Hc Hk NE. destruct s; cbn [pholds pt_reg pt_cache pt_lm pt_qt pt_qg]; try tauto.
        * apply (p_live_delete_other lm u li LU UNIQ). rewrite ECH. congruence.
        * rewrite HQ. unfold e. cbn [qe_chunk]. split; [intros [H|H]; [exact H| exfalso; apply NE; congruence] | intros H; left; exact H].
        * apply HB.
    - (* [comment removed for export] *)
      apply (partition_same (PT reg cache lm qt qg)); [exact P| intros; reflexivity|].
      intros c k s0 Hc Hk. destruct s0; cbn [pholds pt_reg pt_cache pt_lm pt_qt pt_qg]; try tauto.
      + apply (p_live_delete_other lm u li LU UNIQ). rewrite ECH. discriminate.
      + rewrite HQ. unfold e. cbn [qe_chunk]. split; [intros [H|H]; [exact H| discriminate] | intros H; left; exact H].
      + apply HB.
  Qed.

  Lemma pfun_free_push_last : qt <> [] -> pfun (PT reg cache (delete u lm) (qpush_last qt e) qg).
  Proof. intros NE. apply pfun_free_gen; [apply p_quar_push_last; exact NE | apply p_batch_push_last; exact NE]. Qed.
End FreePartition.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qpush_last_emptybatch : forall qt kb e, qpush_last (qt ++ [BA kb []]) e = qpush_new qt kb e.
Proof.
  intros qt kb e. rewrite (qpush_last_shape (qt ++ [BA kb []]) e ltac:(intros H; apply app_eq_nil in H; destruct H; discriminate)).
  rewrite removelast_app by discriminate. cbn [removelast]. rewrite app_nil_r, last_last. reflexivity.
Qed.

Section NewBatch.
  Variables (reg : Z -> region) (cache : Z -> pcache) (lm : gmap Z liveinfo) (qt qg : list batch) (kb : Z).
  Let c24 := kQuarantineBatchClass.
  Let ks := pk_chunks (cache c24).
  Hypothesis P : pfun (PT reg cache lm qt qg).
  Hypothesis ND : NoDup ks.
  Hypothesis NE : ks <> [].
  Hypothesis KB : kb = last ks 0.
  Hypothesis KR : 0 <= kb < carved_count_ reg c24.
  Definition nb_cache : Z -> pcache := cache_set cache c24 (removelast ks).
  Definition nb_qt : list batch := qt ++ [BA kb []].

  Lemma c24_range : 1 <= c24 <= 30. Proof. subst c24. unfold kQuarantineBatchClass. lia. Qed.

  Lemma kb_in : In kb ks.
  Proof. rewrite KB. rewrite (app_removelast_last 0 NE) at 2. apply in_app_iff. right. left. reflexivity. Qed.
  Lemma removelast_in_iff : forall k, In k (removelast ks) <-> In k ks /\ k <> kb.
  Proof.
    intros k. pose proof (app_removelast_last 0 NE) as E. rewrite <- KB in E. split.
    - intros H. split; [rewrite E; apply in_app_iff; left; exact H|].
      intros ->. rewrite E in ND. apply (proj1 (list.NoDup_app _ _)) in ND. destruct ND as (_ & DJ & _).
      apply (DJ kb); apply list_elem_of_In; [exact H| left; reflexivity].
    - intros [H NK]. rewrite E in H. apply in_app_iff in H as [H|[H|[]]]; [exact H| congruence].
  Qed.

  Lemma pfun_newbatch : pfun (PT reg nb_cache lm nb_qt qg).
  Proof.
    apply (partition_move (PT reg cache lm qt qg) _ c24 kb PC PB P); cbn [pt_reg pt_cache pt_lm pt_qt pt_qg].
    - intros; reflexivity.
    - exact c24_range.
    - exact KR.
    - exact kb_in.
    - intros s. destruct s; cbn [pholds pt_reg pt_cache pt_lm pt_qt pt_qg].
      + split; [intros H; right; split; [discriminate| exact H] | intros [H|[_ H]]; [discriminate| exact H]].
      + unfold nb_cache. rewrite p_cached_set. unfold p_cached_. rewrite removelast_in_iff.
        split; [intros [[_ [_ H]]|[H _]]; congruence | intros [H|[H _]]; [discriminate| congruence]].
      + split; [intros H; right; split; [discriminate| exact H] | intros [H|[_ H]]; [discriminate| exact H]].
      + unfold nb_qt, p_quar_. rewrite !q_entries_app. cbn [q_entries flat_map ba_entries app]. rewrite app_nil_r.
        split; [intros H; right; split; [discriminate| exact H] | intros [H|[_ H]]; [discriminate| exact H]].
      + unfold nb_qt, p_batch_, batch_indices_. rewrite <- app_assoc. cbn [app]. rewrite !map_app. cbn [map ba_idx]. rewrite !in_app_iff. cbn [In].
        split; [intros _; left; reflexivity|]. intros _. split; [reflexivity|]. right. left. reflexivity.
    - intros c k s Hc Hk NEQ. destruct s; cbn [pholds pt_reg pt_cache pt_lm pt_qt pt_qg]; try tauto.
      + unfold nb_cache. rewrite p_cached_set. unfold p_cached_. rewrite removelast_in_iff. subst c24.
        destruct (Z.eq_dec c kQuarantineBatchClass) as [->|NC].
        * split; [intros [[_ [H _]]|[H _]]; [exact H| congruence] | intros H; left; split; [reflexivity| split; [exact H| congruence]]].
        * split; [intros [[H _]|[_ H]]; [congruence| exact H] | intros H; right; split; [exact NC| exact H]].
      + unfold nb_qt, p_quar_. rewrite !q_entries_app. cbn [q_entries flat_map ba_entries app]. rewrite app_nil_r. tauto.
      + unfold nb_qt, p_batch_, batch_indices_. rewrite <- app_assoc. cbn [app]. rewrite !map_app. cbn [map ba_idx]. rewrite !in_app_iff. cbn [In].
        subst c24. split; [| tauto]. intros [Hc' [H|[H|H]]]; [split; [exact Hc'| left; exact H] | exfalso; apply NEQ; congruence | split; [exact Hc'| right; exact H]].
  Qed.
End NewBatch.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ql_pop (ql : list batch) : list batch :=
  match ql with
  | BA i (_ :: es) :: R => BA i es :: R
  | _ => ql
  end.

Section EntryPop.
  Variables (qt qg : list batch) (i : Z) (e : qentry) (es : list qentry) (R : list batch).
  Let ql := BA i (e :: es) :: R.
  Let ql' := BA i es :: R.

  (* [comment removed for export] *)

  Hypothesis NDQ : NoDup (map qe_chunk (q_entries (qt ++ (qg ++ ql)))).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End EntryPop.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RecPrimPartition.
  Variables (reg : Z -> region) (cache : Z -> pcache) (lm : gmap Z liveinfo) (qt qg : list batch).
  Variables (i : Z) (e : qentry) (es : list qentry) (R : list batch) (c0 k0 fa' : Z).
  Let ql := BA i (e :: es) :: R.
  Let ql' := BA i es :: R.
  Hypothesis P : pfun (PT reg cache lm qt (qg ++ ql)).
  Hypothesis NDQ : NoDup (map qe_chunk (q_entries (qt ++ (qg ++ ql)))).
  Hypothesis ECH : qe_chunk e = ChP (CP c0 k0).
  Hypothesis Hc0 : 1 <= c0 <= 30.
  Hypothesis Hk0 : 0 <= k0 < carved_count_ reg c0.
  Hypothesis NDC : NoDup (pk_chunks (cache c0)).
  Hypothesis CRG : forall k, In k (pk_chunks (cache c0)) -> 0 <= k < carved_count_ reg c0.

  Let cache' := recp_cache cache c0 k0.
  Let reg' := recp_reg reg cache c0 k0 fa'.
  Let out := snd (cache_push_list (pk_chunks (cache c0)) (max_count c0) k0).
  Let ks' := fst (cache_push_list (pk_chunks (cache c0)) (max_count c0) k0).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Let Tmid := PT reg' (cache_set cache c0 (drain_keep (pk_chunks (cache c0)) (Z.to_nat (max_count c0 / 2)))) lm qt (qg ++ ql).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
End RecPrimPartition.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BatchPop.
  Variables (qt qg : list batch) (i : Z) (R : list batch).
  Let ql := BA i [] :: R.
  Hypothesis NDB : NoDup (batch_indices_ qt (qg ++ ql)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End BatchPop.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RecBatchPartition.
  Variables (reg : Z -> region) (cache : Z -> pcache) (lm : gmap Z liveinfo) (qt qg : list batch).
  Variables (i : Z) (R : list batch) (fa' : Z).
  Let c0 := kQuarantineBatchClass.
  Let ql := BA i [] :: R.
  Hypothesis P : pfun (PT reg cache lm qt (qg ++ ql)).
  Hypothesis NDB : NoDup (batch_indices_ qt (qg ++ ql)).
  Hypothesis Hi : 0 <= i < carved_count_ reg c0.
  Hypothesis NDC : NoDup (pk_chunks (cache c0)).

  Let cache' := recp_cache cache c0 i.
  Let reg' := recp_reg reg cache c0 i fa'.
  Let out := snd (cache_push_list (pk_chunks (cache c0)) (max_count c0) i).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End RecBatchPartition.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PrimFree.
  Variables (lm : gmap Z liveinfo) (qt qg : list batch) (paid : Z -> list Z) (pcred u : Z) (li : liveinfo).
  Hypothesis WN : wf_prim_ lm qt qg paid pcred.
  Hypothesis LU : lm !! u = Some li.

  Lemma p_live_delete_back : forall c k, p_live_ (delete u lm) c k -> p_live_ lm c k.
  Proof. intros c k (u0 & n0 & H). rewrite lookup_delete_Some in H. destruct H as [_ H]. exists u0, n0. exact H. Qed.
  Lemma p_live_of_chunk : forall c k, li_chunk li = ChP (CP c k) -> p_live_ lm c k.
  Proof. intros c k E. exists u, (li_n li). rewrite LU. destruct li as [ch n]; cbn in E |- *. rewrite E. reflexivity. Qed.

  Lemma wf_prim_free_push_last : qt <> [] -> wf_prim_ (delete u lm) (qpush_last qt (QE (li_chunk li) (li_n li))) qg paid pcred.
  Proof.
    intros NE. destruct WN as (P0 & PS & PD). split; [exact P0|]. split; [exact PS|].
    intros c k Hc [V|Q]; apply (PD c k Hc).
    - left. exact (p_live_delete_back c k V).
    - apply (proj1 (p_quar_push_last qt qg _ NE c k)) in Q. destruct Q as [Q|E]; [right; exact Q| left]. cbn [qe_chunk] in E. exact (p_live_of_chunk c k E).
  Qed.
  Lemma wf_prim_free_push_new : forall kb, wf_prim_ (delete u lm) (qpush_new qt kb (QE (li_chunk li) (li_n li))) qg paid pcred.
  Proof.
    intros kb. destruct WN as (P0 & PS & PD). split; [exact P0|]. split; [exact PS|].
    intros c k Hc [V|Q]; apply (PD c k Hc).
    - left. exact (p_live_delete_back c k V).
    - destruct Q as (n & Hn). unfold p_quar_. rewrite q_entries_app in Hn |- *. rewrite qpush_new_entries in Hn.
      rewrite !in_app_iff in Hn. cbn [In] in Hn. destruct Hn as [[Hn|[Hn|[]]]|Hn].
      + right. exists n. apply in_app_iff. left. exact Hn.
      + left. injection Hn as E _. exact (p_live_of_chunk c k E).
      + right. exists n. apply in_app_iff. right. exact Hn.
  Qed.
End PrimFree.
