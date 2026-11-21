(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import ITree Nodes CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import Prelim Monad MSafe MSafeP CMonad CLogic Stdio HarnessC Adapter AdapterC Driver FreshIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ExFlushIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Section TargetSafeC.
Context {St ptr : Type}.
Variable FM : flush_model.
Variable raw_malloc : Z -> M St (option ptr).
Variable raw_free : ptr -> M St unit.
Variable fresh : St -> St -> ptr -> bool.
Variable emit : Z -> M St unit.
Variable own : list (ptr * Z) -> Z -> assn St.

Hypothesis Hm : forall X k n s0, 0 <= n <= 2^62 -> FPRE X k n ->
  mspecP (fun s mo => s = s0 /\ own X k s mo) (raw_malloc n)
         (fun r s mo => match r with
                        | Some p => own ((p, n) :: X) (k + 1) s mo /\ n < 2^63 /\ (KREQ n -> fresh s0 s p = true)
                        | None => False
                        end).
Hypothesis Hf : forall X k p n, mspecP (own ((p, n) :: X) k) (raw_free p) (fun _ => own X k).
Hypothesis Hperm : forall X Y k s mo, Permutation X Y -> own X k s mo -> own Y k s mo.
Hypothesis Hkle : forall X k k' s mo, k <= k' -> own X k s mo -> own X k' s mo.
Hypothesis Hemit : forall X k v, mspecP (own X k) (emit v) (fun _ => own X k).
Definition PIECE_MAX : Z := 1048576.
Hypothesis Hfpr : forall X k ps, Forall (fun p => zlength p <= PIECE_MAX) ps -> mspecP (own X k) (stderr_fprintf ps) (fun _ => own X k).
Hypothesis Hfwr : forall X k bs, zlength bs <= PIECE_MAX -> mspecP (own X k) (stderr_fwrite bs) (fun _ => own X k).

Local Ltac retP := apply mspecP_ret; intros ? ? HH; exact HH.

Lemma creq_spec : forall X k n, 0 <= n <= 2^62 -> FPRE X k n ->
  mspecP (own X k) (creq raw_malloc n) (fun p => own ((p, n) :: X) (k + 1)).
Proof.
  intros X k n Hn HF. unfold creq. apply mspecP_pointwise. intros s0 mo0 H0.
  eapply mspecP_bind.
  { eapply mspecP_pre; [apply (Hm X k n s0 Hn HF)|]. intros s mo [-> ->]. split; [reflexivity| exact H0]. }
  intros [p|]; cbn beta iota.
  - apply mspecP_ret. intros s mo (H & _ & _). exact H.
  - apply mspecP_false.
Qed.

Lemma zreq_spec : forall X k n, 0 <= n <= 2^62 -> KREQ n -> FPRE X k n ->
  mspecP (own X k) (zreq raw_malloc fresh n) (fun p => own ((p, n) :: X) (k + 1)).
Proof.
  intros X k n Hn HK HF. unfold zreq.
  eapply mspecP_bind; [apply mspecP_get|]. intros s0.
  eapply mspecP_bind. { eapply mspecP_pre; [apply (Hm X k n s0 Hn HF)|]. intros s mo [E H]. split; [symmetry; exact E| exact H]. }
  intros [p|]; cbn beta iota; [| apply mspecP_false].
  eapply mspecP_bind; [apply mspecP_get|]. intros s1.
  apply mspecP_if; intros E.
  - apply mspecP_ret. intros s mo (-> & H & _ & _). exact H.
  - eapply mspecP_pre; [apply mspecP_munr|]. intros s mo (-> & _ & _ & HFr). rewrite (HFr HK) in E. discriminate.
Qed.

Lemma fmt_u_length : forall fuel n acc, (length (digits_aux fuel n acc) <= fuel + length acc)%nat.
Proof.
  induction fuel as [|f IH]; intros n acc; cbn [digits_aux]; [lia|].
  destruct (n =? 0); [cbn; lia|]. etransitivity; [apply IH|]. cbn. lia.
Qed.
Lemma pieces_zerr_short : forall msg e, zlength msg <= PIECE_MAX -> Forall (fun p => zlength p <= PIECE_MAX) (pieces_zerr msg e).
Proof.
  intros msg e HM. unfold pieces_zerr, zconv_pieces, fmt_u.
  pose proof (fmt_u_length 20 e []) as L1. pose proof (fmt_u_length 20 (- e) []) as L2. cbn [length] in L1, L2.
  destruct (e =? 0); [|destruct (e <? 0)]; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; try exact HM; unfold zlength, PIECE_MAX; cbn -[digits_aux]; lia.
Qed.
Lemma diag_zerr_spec : forall X k msg e, zlength msg <= PIECE_MAX -> mspecP (own X k) (diag_zerr msg e) (fun _ => own X k).
Proof. intros X k msg e HM. unfold diag_zerr. apply Hfpr. apply pieces_zerr_short. exact HM. Qed.
Lemma msg_deflateEnd_short : zlength MSG_DEFLATEEND <= PIECE_MAX. Proof. unfold MSG_DEFLATEEND, zlength, PIECE_MAX. cbn. lia. Qed.
Lemma msg_inflate_short : zlength MSG_INFLATE <= PIECE_MAX. Proof. unfold MSG_INFLATE, zlength, PIECE_MAX. cbn. lia. Qed.
Lemma msg_inflateSync_short : zlength MSG_INFLATESYNC <= PIECE_MAX. Proof. unfold MSG_INFLATESYNC, zlength, PIECE_MAX. cbn. lia. Qed.

Definition ENTRY (X0 : list (ptr * Z)) (k : Z) : Prop := C31 X0 <= 4 /\ C40 X0 <= 4 /\ C44 X0 <= 2 /\ 0 <= k <= 89.
Lemma live_at_cp : forall X0 k n, ENTRY X0 k -> 0 <= n -> FPRE X0 k n.
Proof. intros X0 k n (A & B & C & K) Hn. unfold FPRE. lia. Qed.
Lemma live_at_up : forall X0 k cp cb n, ENTRY X0 k -> FPRE ((cp, cb) :: X0) (k + 1) n.
Proof.
  intros X0 k cp cb n (A & B & C & K). unfold FPRE, C31, C40, C44 in *.
  pose proof (cntr_cons_le 5437 8172 cp cb X0). pose proof (cntr_cons_le 32749 37436 cp cb X0). pose proof (cntr_cons_le 65517 74876 cp cb X0). lia.
Qed.
Lemma live_at_s : forall X0 k cp cb up n j, ENTRY X0 k -> 0 <= j <= 1 -> FPRE ((up, n) :: (cp, cb) :: X0) (k + 2 + j) 5968.
Proof.
  intros X0 k cp cb up n j (A & B & C & K) Hj. unfold FPRE, C31, C40, C44 in *.
  pose proof (cntr_cons_le 5437 8172 up n ((cp, cb) :: X0)). pose proof (cntr_cons_le 5437 8172 cp cb X0). lia.
Qed.
Lemma live_at_dblk : forall (X : list (ptr * Z)) k, 0 <= k <= 98 -> C44 X <= 55 -> FPRE X k 65536.
Proof. intros X k K C. unfold FPRE. lia. Qed.
Lemma live_at_p : forall X0 k cp cb up n j, ENTRY X0 k -> 0 <= j <= 6 -> FPRE ((up, n) :: (cp, cb) :: X0) (k + 2 + j) 7176.
Proof.
  intros X0 k cp cb up n j (A & B & C & K) Hj. unfold FPRE, C31, C40, C44 in *.
  pose proof (cntr_cons_le 5437 8172 up n ((cp, cb) :: X0)). pose proof (cntr_cons_le 5437 8172 cp cb X0). lia.
Qed.
Lemma live_at_wd : forall (X : list (ptr * Z)) k, 0 <= k <= 98 -> C40 X <= 55 -> FPRE X k 32768.
Proof. intros X k K C. unfold FPRE. lia. Qed.
Lemma cntr_peel lo hi (p : ptr) n X b : cntr lo hi X <= b - 1 -> cntr lo hi ((p, n) :: X) <= b.
Proof. intros H. pose proof (cntr_cons_le lo hi p n X). lia. Qed.
Ltac cnt55 :=
  repeat match goal with x := _ : list _ |- _ => subst x end;
  unfold ENTRY, C31, C40, C44 in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat (apply cntr_peel); lia.

Lemma test_flush_spec : forall X0 k cp cb up n d, ENTRY X0 k ->
  mspecP (own ((up, n) :: (cp, cb) :: X0) (k + 2)) (test_flush_m FM raw_malloc raw_free fresh d n)
         (fun _ => own ((up, n) :: (cp, cb) :: X0) (k + 7)).
Proof.
  intros X0 k cp cb up n d HE. pose proof HE as (_ & _ & _ & K). unfold test_flush_m, DSTATE_N, DBLK_N.
  set (X := (up, n) :: (cp, cb) :: X0).
  eapply mspecP_bind; [apply zreq_spec; [lia| unfold KREQ; lia| replace (k + 2) with (k + 2 + 0) by lia; apply (live_at_s X0 k cp cb up n 0 HE); lia]|]. intros s.
  eapply mspecP_bind; [apply zreq_spec; [lia| unfold KREQ; lia| apply live_at_dblk; [lia| cnt55]]|]. intros w.
  eapply mspecP_bind; [apply zreq_spec; [lia| unfold KREQ; lia| apply live_at_dblk; [lia| cnt55]]|]. intros pv.
  eapply mspecP_bind; [apply zreq_spec; [lia| unfold KREQ; lia| apply live_at_dblk; [lia| cnt55]]|]. intros hd.
  eapply mspecP_bind; [apply zreq_spec; [lia| unfold KREQ; lia| apply live_at_dblk; [lia| cnt55]]|]. intros pb.
  replace (k + 2 + 1 + 1 + 1 + 1 + 1) with (k + 7) by lia.
  eapply mspecP_seq; [apply Hf|]. intros _.
  eapply mspecP_seq; [apply Hf|]. intros _.
  eapply mspecP_seq; [apply Hf|]. intros _.
  eapply mspecP_seq; [apply Hf|]. intros _.
  eapply mspecP_seq; [apply Hf|]. intros _.
  apply mspecP_if; intros _.
  - eapply mspecP_seq; [apply diag_zerr_spec; apply msg_deflateEnd_short|]. intros _. retP.
  - retP.
Qed.

Definition leak_shape (LK : list (ptr * Z)) : Prop :=
  LK = [] \/ (exists p, LK = [(p, 7176)]) \/ (exists p w, LK = [(w, 32768); (p, 7176)]).

Lemma leak_counts : forall LK, leak_shape LK -> C31 LK <= 1 /\ C40 LK <= 1 /\ C44 LK = 0 /\ (length LK <= 2)%nat.
Proof.
  intros LK [-> |[[p ->]|[p [w ->]]]]; unfold C31, C40, C44; rewrite ?cntr_cons, ?cntr_nil; cbn; lia.
Qed.

Lemma finish_sync_spec : forall X k p (w : option ptr) rc,
  mspecP (own (match w with Some wd => [(wd, 32768)] | None => [] end ++ (p, 7176) :: X) k) (finish_sync raw_free p w rc)
         (fun _ s mo => exists LK, own (LK ++ X) k s mo /\ leak_shape LK).
Proof.
  intros X k p w rc. unfold finish_sync. apply mspecP_if; intros _.
  - eapply mspecP_post.
    { destruct w as [wd|]; cbn [app]; unfold inflate_end; [eapply mspecP_seq; [apply Hf|]; intros _; apply Hf | apply Hf]. }
    cbv beta. intros _ s mo H. exists []. split; [exact H | left; reflexivity].
  - eapply mspecP_post; [apply Hfwr; unfold MSG_SHOULD, zlength, PIECE_MAX; cbn; lia|]. cbv beta. intros _ s mo H.
    destruct w as [wd|]; cbn [app] in H.
    + exists [(wd, 32768); (p, 7176)]. split; [exact H | right; right; exists p, wd; reflexivity].
    + exists [(p, 7176)]. split; [exact H | right; left; exists p; reflexivity].
Qed.

Lemma test_sync_spec : forall X0 k cp cb up n c clen, ENTRY X0 k ->
  mspecP (own ((up, n) :: (cp, cb) :: X0) (k + 7)) (test_sync_m FM raw_malloc raw_free fresh c clen n)
         (fun _ s mo => exists LK k', own (LK ++ (up, n) :: (cp, cb) :: X0) k' s mo /\ leak_shape LK /\ k + 8 <= k' <= k + 9).
Proof.
  intros X0 k cp cb up n c clen HE. pose proof HE as (_ & _ & _ & K). unfold test_sync_m, ISTATE_N, WIN_N.
  set (X := (up, n) :: (cp, cb) :: X0).
  eapply mspecP_bind; [apply zreq_spec; [lia| unfold KREQ; lia| replace (k + 7) with (k + 2 + 5) by lia; apply (live_at_p X0 k cp cb up n 5 HE); lia]|]. intros p. cbv beta.
  replace (k + 7 + 1) with (k + 8) by lia.
  destruct (fm_i1 FM c n) as [|e].
  - destruct (fm_is FM c clen n) as [|e].
    + destruct (fm_i2 FM c clen n) as [|rc].
      *
        eapply mspecP_bind; [apply zreq_spec; [lia| unfold KREQ; lia| apply live_at_wd; [lia| cnt55]]|]. intros wd. cbv beta.
        replace (k + 8 + 1) with (k + 9) by lia.
        eapply mspecP_post; [apply (finish_sync_spec X (k + 9) p (Some wd))|]. cbv beta.
        intros _ s mo (LK & H & HL). exists LK, (k + 9). split; [exact H|]. split; [exact HL | lia].
      *
        eapply mspecP_post; [apply (finish_sync_spec X (k + 8) p None)|]. cbv beta.
        intros _ s mo (LK & H & HL). exists LK, (k + 8). split; [exact H|]. split; [exact HL | lia].
    +
      eapply mspecP_post; [apply diag_zerr_spec; apply msg_inflateSync_short|]. cbv beta. intros _ s mo H. exists [(p, 7176)], (k + 8).
      split; [exact H|]. split; [right; left; exists p; reflexivity| lia].
  -
    eapply mspecP_post; [apply diag_zerr_spec; apply msg_inflate_short|]. cbv beta. intros _ s mo H. exists [(p, 7176)], (k + 8).
    split; [exact H|]. split; [right; left; exists p; reflexivity| lia].
Qed.

Lemma CLEN_small : forall n, 0 <= n -> fuzz_skip n = false -> 0 <= CLEN n <= 2^62.
Proof.
  intros n Hn Hs. unfold fuzz_skip, KMAX in Hs. apply Bool.orb_false_iff in Hs as [H1 H2]. apply Z.leb_gt in H1. apply Z.ltb_ge in H2.
  pose proof (CLEN_ge n Hn). pose proof (CLEN_lt32 n ltac:(lia)). lia.
Qed.

Lemma fuzz_one_m_spec : forall X0 k d, ENTRY X0 k ->
  mspecP (own X0 k) (fuzz_one_m FM raw_malloc raw_free fresh d)
         (fun _ s mo => exists LK k', own (LK ++ X0) k' s mo /\ leak_shape LK /\ k <= k' <= k + 9).
Proof.
  intros X0 k d HE. pose proof HE as (_ & _ & _ & K). unfold fuzz_one_m.
  apply mspecP_if; [intros _| intros Hsk].
  { apply mspecP_ret. intros s mo H. exists [], k. split; [exact H|]. split; [left; reflexivity| lia]. }
  pose proof (CLEN_small (zlength d) ltac:(unfold zlength; lia) Hsk) as [CB0 CB1].
  eapply mspecP_bind; [apply creq_spec; [split; [exact CB0| exact CB1]| apply live_at_cp; [exact HE| exact CB0]]|].
  intros cp.
  eapply mspecP_bind; [apply creq_spec; [unfold fuzz_skip, KMAX, zlength in *; lia| apply live_at_up; exact HE]|]. intros up.
  replace (k + 1 + 1) with (k + 2) by lia.
  eapply mspecP_bind; [apply (test_flush_spec X0 k cp _ up _ d HE)|]. intros clen.
  eapply mspecP_bind; [apply (test_sync_spec X0 k cp _ up _ _ clen HE)|]. intros u. cbv beta.
  apply mspecP_exI. intros LK. apply mspecP_exI. intros k'.
  eapply mspecP_pre with (P := fun s mo => own ((cp, CLEN (zlength d)) :: (up, zlength d) :: LK ++ X0) k' s mo /\ (leak_shape LK /\ k + 8 <= k' <= k + 9)).
  2:{ intros s mo (H & HL & HK'). split; [| split; [exact HL| exact HK']].
      eapply Hperm; [| exact H].
      change ((cp, CLEN (zlength d)) :: (up, zlength d) :: LK ++ X0) with ([(cp, CLEN (zlength d)); (up, zlength d)] ++ (LK ++ X0)).
      change (LK ++ (up, zlength d) :: (cp, CLEN (zlength d)) :: X0) with (LK ++ [(up, zlength d); (cp, CLEN (zlength d))] ++ X0).
      rewrite !app_assoc. apply Permutation_app_tail. etransitivity; [apply Permutation_app_comm|]. apply Permutation_app_tail. apply perm_swap. }
  apply mspecP_pure. intros [HL HK'].
  eapply mspecP_seq; [apply Hf|]. intros _. eapply mspecP_seq; [apply Hf|]. intros _.
  apply mspecP_ret. intros s mo H. exists LK, k'. split; [exact H|]. split; [exact HL| lia].
Qed.

Lemma fuzz_one_spec : forall X0 k d, ENTRY X0 k ->
  cspecP (own X0 k) (HarnessC.fuzz_one FM raw_malloc raw_free fresh d)
         (fun _ s mo => exists LK k', own (LK ++ X0) k' s mo /\ leak_shape LK /\ k <= k' <= k + 9).
Proof. intros X0 k d HE. unfold HarnessC.fuzz_one. apply cspecP_lift. apply fuzz_one_m_spec. exact HE. Qed.

Definition CALLS_ENTRY (X : list (ptr * Z)) (k : Z) (ncalls : nat) : Prop :=
  C31 X + Z.of_nat ncalls <= 5 /\ C40 X + Z.of_nat ncalls <= 5 /\ C44 X <= 2 /\ 0 <= k /\ k + 9 * Z.of_nat ncalls <= 98.

Local Notation fuzz_one := (HarnessC.fuzz_one FM raw_malloc raw_free fresh).

Lemma run_calls_spec : forall ncalls X k payload rc, CALLS_ENTRY X k ncalls ->
  cspecP (own X k) (AdapterC.run_calls fuzz_one emit ncalls payload rc)
         (fun _ s mo => exists LK k', own (LK ++ X) k' s mo /\ k <= k' <= k + 9 * Z.of_nat ncalls).
Proof.
  induction ncalls as [|nc IH]; intros X k payload rc (A & B & C & K0 & K); cbn [AdapterC.run_calls].
  - apply cspecP_ret. intros s mo H. exists [], k. split; [exact H| cbn; lia].
  - eapply cspecP_bind.
    { apply fuzz_one_spec. split; [lia|]. split; [lia|]. split; [exact C| lia]. }
    intros rc'. apply cspecP_exI. intros LK. apply cspecP_exI. intros k'. apply cspecP_pure. intros [HL HK'].
    pose proof (leak_counts LK HL) as (L1 & L2 & L3 & L4).
    eapply cspecP_seq; [apply cspecP_lift, Hemit|]. intros _.
    eapply cspecP_post; [apply (IH (LK ++ X) k')|].
    { unfold CALLS_ENTRY, C31, C40, C44 in *. rewrite !cntr_app. cbn [length] in K. split; [lia|]. split; [lia|]. split; [lia|]. lia. }
    cbv beta. intros _ s mo (LK2 & k2 & H & HK2). exists (LK2 ++ LK), k2. split; [rewrite <- app_assoc; exact H| lia].
Qed.

Lemma payload_copy_spec : forall X k payload, 0 <= k -> zlength payload <= 2^62 -> FPRE X k (zlength payload) ->
  mspecP (own X k) (AdapterC.payload_copy raw_malloc payload)
        (fun a s mo => match a with
                       | None => False
                       | Some None => own X k s mo
                       | Some (Some p) => own ((p, zlength payload) :: X) (k + 1) s mo
                       end).
Proof.
  intros X k payload Hk HL HF. unfold AdapterC.payload_copy.
  apply mspecP_if; intros _; [retP|].
  apply mspecP_pointwise. intros s0 mo0 H0.
  eapply mspecP_bind.
  { eapply mspecP_pre; [apply (Hm X k (zlength payload) s0); [unfold zlength in *; lia| exact HF]|]. intros s mo [-> ->]. auto. }
  intros [p|]; cbn beta iota; [| apply mspecP_false]. apply mspecP_ret. intros s mo (H & _). exact H.
Qed.

Definition TR_ENTRY (X : list (ptr * Z)) (k : Z) : Prop := C31 X = 0 /\ C40 X = 0 /\ C44 X <= 1 /\ 0 <= k <= 12.

Theorem target_run_spec : forall X k cfg payload, zlength payload <= 2^62 -> TR_ENTRY X k ->
  cspecP (own X k) (AdapterC.target_run raw_malloc raw_free fuzz_one emit cfg payload)
         (fun _ s mo => exists LK k', own (LK ++ X) k' s mo /\ 0 <= k').
Proof.
  intros X k cfg payload HL (A & B & C & K). unfold AdapterC.target_run.
  assert (NC : Z.of_nat (Z.to_nat (1 + Z.land cfg 3)) <= 4).
  { assert (E : Z.land cfg 3 = cfg mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z.mod_pos_bound cfg 4 ltac:(lia)). rewrite E. rewrite Z2Nat.id; lia. }
  eapply cspecP_bind; [apply cspecP_lift, payload_copy_spec; [lia| exact HL| unfold FPRE; lia]|].
  intros [[p|]|]; cbn beta iota.
  -
    eapply cspecP_bind.
    { apply run_calls_spec. unfold CALLS_ENTRY, C31, C40, C44 in *.
      pose proof (cntr_cons_le 5437 8172 p (zlength payload) X). pose proof (cntr_cons_le 32749 37436 p (zlength payload) X).
      pose proof (cntr_cons_le 65517 74876 p (zlength payload) X). lia. }
    intros rc. apply cspecP_exI. intros LK. apply cspecP_exI. intros k'. apply cspecP_pure. intros HK'.
    eapply cspecP_seq.
    { apply cspecP_lift. eapply mspecP_pre; [apply (Hf (LK ++ X) k' p (zlength payload))|].
      intros s mo H. eapply Hperm; [| exact H]. symmetry. apply Permutation_middle. }
    intros _. apply cspecP_ret. intros s mo H. exists LK, k'. split; [exact H| lia].
  -
    eapply cspecP_bind; [apply run_calls_spec; unfold CALLS_ENTRY; lia|]. intros rc.
    apply cspecP_exI. intros LK. apply cspecP_exI. intros k'. apply cspecP_pure. intros HK'.
    eapply cspecP_seq; [apply cspecP_lift; retP|]. intros _.
    apply cspecP_ret. intros s mo H. exists LK, k'. split; [exact H| lia].
  - apply cspecP_false.
Qed.

End TargetSafeC.
