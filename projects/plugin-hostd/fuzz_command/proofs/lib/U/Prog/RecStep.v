From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require answer_c.
Import ListNotations.
Open Scope Z_scope.

Definition rec_entry (gr sc : Z) (R : rstate) : Z :=
  if Nat.ltb (length (r_calls R)) 16 then gr + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) else sc.

Lemma rec_record_lt : forall R fn As, (length (r_calls R) < 16)%nat ->
  rec_record R fn As = set_calls R (r_calls R ++ [(fn, As)]).
Proof. intros R fn As H. unfold rec_record. apply Nat.ltb_lt in H. rewrite H. reflexivity. Qed.

Lemma rec_record_full : forall R fn As, length (r_calls R) = 16%nat ->
  rec_record R fn As = set_spill R (fn, As).
Proof. intros R fn As H. unfold rec_record. rewrite H. reflexivity. Qed.

Lemma rec_entry_lt : forall gr sc R, (length (r_calls R) < 16)%nat ->
  rec_entry gr sc R = gr + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)).
Proof. intros gr sc R H. unfold rec_entry. apply Nat.ltb_lt in H. rewrite H. reflexivity. Qed.

Lemma rec_entry_full : forall gr sc R, length (r_calls R) = 16%nat -> rec_entry gr sc R = sc.
Proof. intros gr sc R H. unfold rec_entry. rewrite H. reflexivity. Qed.

Lemma le8_fn_split : forall fn, 0 <= fn < REC_FN_COUNT ->
  le8 (Z_to_bv 64 fn) = le4 (Z_to_bv 64 fn) ++ le4 (Z_to_bv 64 0).
Proof.
  intros fn H. unfold REC_FN_COUNT in H.
  assert (E : exists k, fn = Z.of_nat k /\ (k < 26)%nat) by (exists (Z.to_nat fn); lia).
  destruct E as [k [-> Hk]].
  do 26 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma nodup_app_disj : forall (X : Type) (l1 l2 : list X) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros X l1 l2 x H H1 H2. apply list_relations.list.NoDup_app in H as (_ & H & _).
  apply (H x); apply list_elem_of_In; assumption.
Qed.

Lemma nodup_fst_disj : forall (l1 l2 : list (Z * Z)) pn qn, NoDup (map fst (l1 ++ l2)) ->
  In pn l1 -> In qn l2 -> fst pn <> fst qn.
Proof.
  intros l1 l2 pn qn H H1 H2 E. rewrite map_app in H.
  apply (nodup_app_disj Z (map fst l1) (map fst l2) (fst pn) H); [apply in_map; exact H1|].
  rewrite E. apply in_map. exact H2.
Qed.

Section Step.
Variable segs : list Segment.

Lemma call_at_blocks : forall bl m a c P pn, call_at segs bl m a c P -> In pn P -> In pn bl.
Proof.
  intros bl m a c P pn (_ & _ & Hl & _ & _ & _ & Hk) Hin.
  destruct (In_nth_error P pn Hin) as [k Ek].
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  exact (proj1 (proj2 (proj2 (Hk k s pn Es Ek)))).
Qed.

Lemma rec_rep_record_lt : forall gr sc L A mem mem' R O fn,
  rec_rep segs gr sc L A mem R O ->
  (length (r_calls R) < 16)%nat -> 0 <= fn < REC_FN_COUNT ->
  bytes_at segs mem' (gr + OFF_NCALLS) (le4 (Z_to_bv 64 (Z.of_nat (length (r_calls R)) + 1))) ->
  bytes_at segs mem' (rec_entry gr sc R + CALL_OFF_FN) (le4 (Z_to_bv 64 fn)) ->
  bytes_at segs mem' (rec_entry gr sc R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 0)) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE ->
     ~ (gr + OFF_NCALLS <= a < gr + OFF_NCALLS + 4) -> ~ (rec_entry gr sc R <= a < rec_entry gr sc R + 8) ->
     mbyte segs mem' a = mbyte segs mem a) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs mem a -> writable_at segs mem' a) ->
  (forall p k i, In (p, k) O -> 0 <= i < k -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) ->
  rec_rep segs gr sc L A mem' (rec_record R fn []) O.
Proof.
  intros gr sc L A mem mem' R O fn (Q & HR & HO) Hn Hfn BN BF BA KG KW KB.
  rewrite (rec_entry_lt gr sc R Hn) in BF, BA, KG.
  rewrite (rec_record_lt R fn [] Hn).
  destruct HR as (HS & HC & HA & HP & HX & HW).
  destruct HS as (S1 & S2 & S3 & S4 & S5).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  assert (KQ : forall pn, In pn (lay_blocks Q) ->
            forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)).
  { intros [p k] Hpn i Hi. apply HO in Hpn. exact (KB p k i Hpn Hi). }
  exists (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)).
  assert (LB : lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat]. rewrite !app_nil_r.
    reflexivity. }
  split; [| rewrite LB; exact HO].
  unfold rep_at, g1_storage, g1_calls, g1_scalars, g1_own, answer_at, reply_at in *.
  cbn [set_calls r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host
       l_calls l_spill l_answer l_reply] in *.
  rewrite LB.
  unfold REC_SIZE, SC_SIZE, OFF_REFUSE, OFF_CODE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_NREPLIES, OFF_REPLY,
    OFF_REPLY_SIZE, OFF_STATE, OFF_HOST, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS in *.
  assert (KR : forall x, gr <= x < gr + 960 -> ~ (gr + 8 <= x < gr + 8 + 4) ->
            ~ (gr + 16 + 56 * Z.of_nat (length (r_calls R)) <= x < gr + 16 + 56 * Z.of_nat (length (r_calls R)) + 8) ->
            mbyte segs mem' x = mbyte segs mem x).
  { intros x H1 H2 H3. apply KG; [left; exact H1 | exact H2 | exact H3]. }
  assert (KS : forall x, sc <= x < sc + 56 -> mbyte segs mem' x = mbyte segs mem x).
  { intros x Hx. unfold iv_apart in S3. apply KG; [right; exact Hx | lia | lia]. }
  split; [| split; [| split; [| split; [| split]]]].
  - refine (conj S1 (conj S2 (conj S3 (conj _ _)))).
    + apply (wr_at_keep segs mem); [exact S4|]. intros i Hi. apply KW. left. lia.
    + apply (wr_at_keep segs mem); [exact S5|]. intros i Hi. apply KW. right. lia.
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ C6))))).
    + rewrite length_app. cbn [length]. lia.
    + rewrite !length_app, C2. reflexivity.
    + rewrite length_app. cbn [length]. replace (Z.of_nat (length (r_calls R) + 1)) with
        (Z.of_nat (length (r_calls R)) + 1) by lia. exact BN.
    + intros i c P Ec EP.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      * rewrite nth_error_app1 in Ec by exact Hi. rewrite nth_error_app1 in EP by (rewrite C2; exact Hi).
        destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
        apply (call_at_keep segs (blocks L A) (blocks L A) mem mem'); [exact Hc | |].
        -- intros x Hx. unfold CALL_SIZE in Hx. apply KR; lia.
        -- intros pn Hpn. split; [exact (call_at_blocks _ _ _ _ _ _ Hc Hpn)|].
           apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
           exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
      * destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
        -- rewrite nth_error_app2 in Ec by lia. rewrite Nat.sub_diag in Ec. cbn in Ec. injection Ec as <-.
           rewrite nth_error_app2 in EP by lia. rewrite C2, Nat.sub_diag in EP. cbn in EP. injection EP as <-.
           split; [|constructor].
           unfold call_at. cbn [fst snd length].
           split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
           split; [exact BF|]. split; [exact BA|]. split; [constructor|].
           intros k s pn Es. destruct k; discriminate.
        -- exfalso. assert (N : nth_error (r_calls R ++ [(fn, [])]) i = None)
             by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
           rewrite N in Ec. discriminate.
    + apply (call_at_keep segs (blocks L A) (blocks L A) mem mem'); [exact C5 | |].
      * intros x Hx. unfold CALL_SIZE in Hx. apply KS. lia.
      * intros pn Hpn. split; [exact (call_at_blocks _ _ _ _ _ _ C5 Hpn)|].
        apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - revert HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [[p k]|] eqn:EA; intros HA; try contradiction.
    + destruct HA as (N1 & N2 & N3 & N4 & N5 & N6 & N7). cbn [fst snd] in *.
      assert (Hq : In (p, k) (lay_blocks Q)).
      { unfold lay_blocks. rewrite EA. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
        left. reflexivity. }
      split; [apply (bytes_at_keep_in segs mem mem' (gr + 912) (gr + 920));
              [exact N1 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia]|].
      split; [exact N2|]. split; [exact N3|]. split; [exact N4|].
      split; [|split; [exact N6 | exact N7]].
      apply (bytes_at_keep segs mem); [exact N5|]. intros i Hi. apply (KQ (p, k) Hq). cbn [snd].
      rewrite length_app in Hi. cbn [length] in Hi. lia.
    + apply (bytes_at_keep_in segs mem mem' (gr + 912) (gr + 920));
        [exact HA | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia].
  - revert HP. destruct (r_reply R) as [y|]; destruct (l_reply Q) as [[p k]|] eqn:EP; intros HP; try contradiction.
    + destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). cbn [fst snd] in *.
      assert (Hq : In (p, k) (lay_blocks Q)).
      { unfold lay_blocks. rewrite EP. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
        left. reflexivity. }
      split; [apply (bytes_at_keep_in segs mem mem' (gr + 928) (gr + 936));
              [exact P1 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia]|].
      split; [apply (bytes_at_keep_in segs mem mem' (gr + 936) (gr + 944));
              [exact P2 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia]|].
      split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|].
      split; [|exact P8].
      apply (bytes_at_keep segs mem); [exact P7|]. intros i Hi. apply (KQ (p, k) Hq). cbn [snd]. lia.
    + destruct HP as [P1 P2].
      split; [apply (bytes_at_keep_in segs mem mem' (gr + 928) (gr + 936));
              [exact P1 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia]|].
      apply (bytes_at_keep_in segs mem mem' (gr + 936) (gr + 944));
        [exact P2 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia].
  - destruct HX as (X1 & X2 & X3 & X4 & X5 & X6).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
    + apply (bytes_at_keep_in segs mem mem' gr (gr + 4));
        [exact X1 | lia | rewrite length_le4; lia | intros x Hx; apply KR; lia].
    + apply (bytes_at_keep_in segs mem mem' (gr + 4) (gr + 8));
        [exact X2 | lia | rewrite length_le4; lia | intros x Hx; apply KR; lia].
    + apply (bytes_at_keep_in segs mem mem' (gr + 920) (gr + 924));
        [exact X3 | lia | rewrite length_le4; lia | intros x Hx; apply KR; lia].
    + apply (bytes_at_keep_in segs mem mem' (gr + 944) (gr + 952));
        [exact X4 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia].
    + apply (bytes_at_keep_in segs mem mem' (gr + 952) (gr + 960));
        [exact X5 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia].
  - exact HW.
Qed.

Lemma g1_storage_keep : forall mem mem' gr sc,
  g1_storage segs mem gr sc ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs mem a -> writable_at segs mem' a) ->
  g1_storage segs mem' gr sc.
Proof.
  intros mem mem' gr sc (S1 & S2 & S3 & S4 & S5) KW.
  refine (conj S1 (conj S2 (conj S3 (conj _ _)))).
  - apply (wr_at_keep segs mem); [exact S4|]. intros i Hi. apply KW. left. lia.
  - apply (wr_at_keep segs mem); [exact S5|]. intros i Hi. apply KW. right. lia.
Qed.

Lemma ans_rep_keep : forall bl bl' mem mem' gr R ans rep,
  answer_at segs bl mem gr (r_answer R) ans -> reply_at segs bl mem gr (r_reply R) rep ->
  (forall x, gr + 912 <= x < gr + 944 -> mbyte segs mem' x = mbyte segs mem x) ->
  (forall pn, In pn (oblk ans ++ oblk rep) -> In pn bl' /\
     forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)) ->
  answer_at segs bl' mem' gr (r_answer R) ans /\ reply_at segs bl' mem' gr (r_reply R) rep.
Proof.
  intros bl bl' mem mem' gr R ans rep HA HP KR KQ.
  unfold answer_at, reply_at in *. unfold OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE in *.
  split.
  - revert HA KQ. destruct (r_answer R) as [t|]; destruct ans as [[p k]|]; intros HA KQ; try contradiction.
    + destruct HA as (N1 & N2 & N3 & N4 & N5 & N6 & N7). cbn [fst snd] in *.
      destruct (KQ (p, k) ltac:(cbn; left; reflexivity)) as [Kin Kp]. cbn [fst snd] in Kp.
      split; [apply (bytes_at_keep_in segs mem mem' (gr + 912) (gr + 920));
              [exact N1 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia]|].
      split; [exact N2|]. split; [exact Kin|]. split; [exact N4|].
      split; [|split; [exact N6 | exact N7]].
      apply (bytes_at_keep segs mem); [exact N5|]. intros i Hi. apply Kp.
      rewrite length_app in Hi. cbn [length] in Hi. lia.
    + apply (bytes_at_keep_in segs mem mem' (gr + 912) (gr + 920));
        [exact HA | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia].
  - revert HP KQ. destruct (r_reply R) as [y|]; destruct rep as [[p k]|]; intros HP KQ; try contradiction.
    + destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). cbn [fst snd] in *.
      destruct (KQ (p, k) ltac:(apply in_or_app; right; cbn; left; reflexivity)) as [Kin Kp]. cbn [fst snd] in Kp.
      split; [apply (bytes_at_keep_in segs mem mem' (gr + 928) (gr + 936));
              [exact P1 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia]|].
      split; [apply (bytes_at_keep_in segs mem mem' (gr + 936) (gr + 944));
              [exact P2 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia]|].
      split; [exact P3|]. split; [exact P4|]. split; [exact Kin|]. split; [exact P6|].
      split; [|exact P8].
      apply (bytes_at_keep segs mem); [exact P7|]. intros i Hi. apply Kp. lia.
    + destruct HP as [P1 P2].
      split; [apply (bytes_at_keep_in segs mem mem' (gr + 928) (gr + 936));
              [exact P1 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia]|].
      apply (bytes_at_keep_in segs mem mem' (gr + 936) (gr + 944));
        [exact P2 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia].
Qed.

Lemma scalars_keep : forall mem mem' gr R, g1_scalars segs mem gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 ->
     mbyte segs mem' x = mbyte segs mem x) ->
  g1_scalars segs mem' gr R.
Proof.
  intros mem mem' gr R HX KR. unfold g1_scalars in *.
  unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  destruct HX as (X1 & X2 & X3 & X4 & X5 & X6).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  - apply (bytes_at_keep_in segs mem mem' gr (gr + 4));
      [exact X1 | lia | rewrite length_le4; lia | intros x Hx; apply KR; lia].
  - apply (bytes_at_keep_in segs mem mem' (gr + 4) (gr + 8));
      [exact X2 | lia | rewrite length_le4; lia | intros x Hx; apply KR; lia].
  - apply (bytes_at_keep_in segs mem mem' (gr + 920) (gr + 924));
      [exact X3 | lia | rewrite length_le4; lia | intros x Hx; apply KR; lia].
  - apply (bytes_at_keep_in segs mem mem' (gr + 944) (gr + 952));
      [exact X4 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia].
  - apply (bytes_at_keep_in segs mem mem' (gr + 952) (gr + 960));
      [exact X5 | lia | rewrite length_le8; lia | intros x Hx; apply KR; lia].
Qed.

Lemma rep_rest_keep : forall bl bl' mem mem' gr R ans rep,
  answer_at segs bl mem gr (r_answer R) ans -> reply_at segs bl mem gr (r_reply R) rep ->
  g1_scalars segs mem gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 912 <= x < gr + 960 -> mbyte segs mem' x = mbyte segs mem x) ->
  (forall pn, In pn (oblk ans ++ oblk rep) -> In pn bl' /\
     forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)) ->
  answer_at segs bl' mem' gr (r_answer R) ans /\ reply_at segs bl' mem' gr (r_reply R) rep /\
  g1_scalars segs mem' gr R.
Proof.
  intros bl bl' mem mem' gr R ans rep HA HP HX KR KQ.
  destruct (ans_rep_keep bl bl' mem mem' gr R ans rep HA HP ltac:(intros x Hx; apply KR; lia) KQ) as [RA RP].
  split; [exact RA|]. split; [exact RP|].
  exact (scalars_keep mem mem' gr R HX ltac:(intros x Hx; apply KR; lia)).
Qed.

Lemma rep_at_blocks : forall bl mem gr sc R Q pn, rep_at segs bl mem gr sc R Q -> In pn (lay_blocks Q) -> In pn bl.
Proof.
  intros bl mem gr sc R Q pn (HS & HC & HA & HP & HX & HW) Hin.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP0 & Hpn).
    destruct (In_nth_error _ _ HP0) as [i Ei].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    exact (call_at_blocks _ _ _ _ _ _ (proj1 (C4 i c P Ec Ei)) Hpn).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (call_at_blocks _ _ _ _ _ _ C5 Hin)|].
    apply in_app_or in Hin as [Hin|Hin].
    + revert HA Hin. unfold answer_at.
      destruct (r_answer R); destruct (l_answer Q) as [pn'|]; intros HA Hin; cbn [oblk In] in Hin; try contradiction.
      destruct Hin as [<-|[]]. exact (proj1 (proj2 (proj2 HA))).
    + revert HP Hin. unfold reply_at.
      destruct (r_reply R); destruct (l_reply Q) as [pn'|]; intros HP Hin; cbn [oblk In] in Hin; try contradiction.
      destruct Hin as [<-|[]]. exact (proj1 (proj2 (proj2 (proj2 (proj2 HP))))).
Qed.

End Step.

Lemma nodup_fst_drop_mid : forall X S Y : list (Z * Z), NoDup (map fst (X ++ S ++ Y)) -> NoDup (map fst (X ++ Y)).
Proof.
  intros X S Y H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup. rewrite !map_app in *.
  apply (Permutation_NoDup (Permutation_app_swap_app _ _ _)) in H. exact (NoDup_app_remove_l _ _ H).
Qed.

Lemma nodup_fst_snoc : forall (l : list (Z * Z)) p k, NoDup (map fst l) -> ~ In p (map fst l) ->
  NoDup (map fst (l ++ [(p, k)])).
Proof.
  intros l p k H N. rewrite map_app. cbn [map fst]. apply list_relations.list.NoDup_app. split; [exact H|]. split.
  - intros x Hx Hp. apply list_elem_of_In in Hx. apply list_elem_of_In in Hp. destruct Hp as [E|[]]. subst.
    exact (N Hx).
  - constructor; [intros Hx; apply list_elem_of_In in Hx; destruct Hx | constructor].
Qed.

Lemma nodup_fst_perm : forall l l' : list (Z * Z), Permutation l l' -> NoDup (map fst l) -> NoDup (map fst l').
Proof.
  intros l l' HP H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
  exact (Permutation_NoDup (Permutation_map fst HP) H).
Qed.

Lemma lay_drop_spill : forall Q pn, NoDup (map fst (lay_blocks Q)) ->
  In pn (lay_blocks (RLay (l_calls Q) [] (l_answer Q) (l_reply Q))) <->
  In pn (lay_blocks Q) /\ ~ In pn (l_spill Q).
Proof.
  intros Q pn H. unfold lay_blocks in *. cbn [l_calls l_spill l_answer l_reply app].
  split.
  - intros Hin. apply in_app_or in Hin as [Hin|Hin].
    + split; [apply in_or_app; left; exact Hin|]. intros Hs.
      apply (nodup_fst_disj _ _ pn pn H Hin); [apply in_or_app; left; exact Hs | reflexivity].
    + split; [apply in_or_app; right; apply in_or_app; right; exact Hin|]. intros Hs.
      rewrite app_assoc in H.
      apply (nodup_fst_disj _ _ pn pn H); [apply in_or_app; right; exact Hs | exact Hin | reflexivity].
  - intros [Hin Hs]. apply in_app_or in Hin as [Hin|Hin]; [apply in_or_app; left; exact Hin|].
    apply in_app_or in Hin as [Hin|Hin]; [contradiction | apply in_or_app; right; exact Hin].
Qed.

Lemma nodup_fst_mid : forall (X S Y : list (Z * Z)) p q, NoDup (map fst (X ++ S ++ Y)) ->
  In p (X ++ Y) -> In q S -> fst p <> fst q.
Proof.
  intros X S Y p q H Hp Hq. apply in_app_or in Hp as [Hp|Hp].
  - apply (nodup_fst_disj X (S ++ Y) p q H Hp). apply in_or_app. left. exact Hq.
  - rewrite app_assoc in H. intros E.
    apply (nodup_fst_disj (X ++ S) Y q p H); [apply in_or_app; right; exact Hq | exact Hp | symmetry; exact E].
Qed.

Lemma spill_others_kept : forall (segs : list Segment) Q bl bl' F mem mem',
  NoDup (map fst (lay_blocks Q)) ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl) ->
  (forall pn, In pn F -> In pn (l_spill Q)) ->
  (forall pn, In pn bl -> In pn bl' \/ In pn F) ->
  (forall a k i, In (a, k) bl -> ~ In a (map fst F) -> 0 <= i < k ->
     mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
  forall pn, In pn (lay_blocks Q) -> ~ In pn (l_spill Q) -> In pn bl' /\
    forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i).
Proof.
  intros segs Q bl bl' F mem mem' H HB HF HP HK [a k] Hin Hs.
  assert (Hbl : In (a, k) bl) by exact (HB _ Hin).
  split; [destruct (HP _ Hbl) as [H1|H1]; [exact H1 | exfalso; exact (Hs (HF _ H1))]|].
  intros i Hi. apply (HK a k i Hbl); [|exact Hi].
  intros Ha. apply in_map_iff in Ha as ([a' k'] & Ea & Hf). cbn [fst] in Ea. subst a'.
  assert (Hm : In (a, k) (lay_blocks (RLay (l_calls Q) [] (l_answer Q) (l_reply Q))))
    by (apply (proj2 (lay_drop_spill Q (a, k) H)); split; assumption).
  unfold lay_blocks in Hm, H. cbn [l_calls l_spill l_answer l_reply app] in Hm.
  exact (nodup_fst_mid _ _ _ (a, k) (a, k') H Hm (HF _ Hf) eq_refl).
Qed.

Lemma perm_snoc_mid : forall (X Y W : list (Z * Z)) a, Permutation (X ++ (Y ++ [a]) ++ W) ((X ++ Y ++ W) ++ [a]).
Proof.
  intros X Y W a. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
  cbn [app]. apply Permutation_cons_append.
Qed.

Lemma lay_perm_lt : forall l0 P S ans rep pk,
  Permutation (lay_blocks (RLay (l0 ++ [P ++ [pk]]) S ans rep)) (lay_blocks (RLay (l0 ++ [P]) S ans rep) ++ [pk]).
Proof.
  intros l0 P S ans rep pk.
  assert (E1 : lay_blocks (RLay (l0 ++ [P ++ [pk]]) S ans rep) = concat l0 ++ (P ++ [pk]) ++ S ++ oblk ans ++ oblk rep).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
    rewrite app_nil_r. rewrite <- !app_assoc. reflexivity. }
  assert (E2 : lay_blocks (RLay (l0 ++ [P]) S ans rep) = concat l0 ++ P ++ S ++ oblk ans ++ oblk rep).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
    rewrite app_nil_r. rewrite <- !app_assoc. reflexivity. }
  rewrite E1, E2. apply perm_snoc_mid.
Qed.

Lemma lay_perm_full : forall lc S ans rep pk,
  Permutation (lay_blocks (RLay lc (S ++ [pk]) ans rep)) (lay_blocks (RLay lc S ans rep) ++ [pk]).
Proof. intros lc S ans rep pk. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply perm_snoc_mid. Qed.

Lemma lay_perm_iff : forall (O l l' : list (Z * Z)) (pk : Z * Z), (forall pn, In pn O <-> In pn l) ->
  Permutation l' (l ++ [pk]) ->
  forall pn, In pn (O ++ [pk]) <-> In pn l'.
Proof.
  intros O l l' pk HO HP pn. split; intros H.
  - apply (Permutation_in _ (Permutation_sym HP)). apply in_app_or in H as [H|H]; apply in_or_app;
      [left; apply HO; exact H | right; exact H].
  - apply (Permutation_in _ HP) in H. apply in_app_or in H as [H|H]; apply in_or_app;
      [left; apply HO; exact H | right; exact H].
Qed.

Section Step2.
Variable segs : list Segment.

Lemma rec_rep_of_rep : forall gr sc L A mem R Q,
  rep_at segs (blocks L A) mem gr sc R Q -> rec_rep segs gr sc L A mem R (lay_blocks Q).
Proof. intros gr sc L A mem R Q H. exists Q. split; [exact H | tauto]. Qed.

Lemma rep_at_record_full : forall gr sc bl bl' mem mem' R Q fn,
  rep_at segs bl mem gr sc R Q ->
  length (r_calls R) = 16%nat -> 0 <= fn < REC_FN_COUNT ->
  bytes_at segs mem' (sc + CALL_OFF_FN) (le4 (Z_to_bv 64 fn)) ->
  bytes_at segs mem' (sc + CALL_OFF_NARGS) (le4 (Z_to_bv 64 0)) ->
  (forall a, gr <= a < gr + REC_SIZE -> mbyte segs mem' a = mbyte segs mem a) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs mem a -> writable_at segs mem' a) ->
  (forall pn, In pn (lay_blocks Q) -> ~ In pn (l_spill Q) -> In pn bl' /\
     forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)) ->
  rep_at segs bl' mem' gr sc (rec_record R fn []) (RLay (l_calls Q) [] (l_answer Q) (l_reply Q)).
Proof.
  intros gr sc bl bl' mem mem' R Q fn HR Hn Hfn BF BA KG KW KB.
  rewrite (rec_record_full R fn [] Hn).
  destruct HR as (HS & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  destruct HW as [HND HAP].
  assert (KB' : forall pn, In pn (lay_blocks (RLay (l_calls Q) [] (l_answer Q) (l_reply Q))) -> In pn bl' /\
            forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)).
  { intros pn Hpn. apply (lay_drop_spill Q pn HND) in Hpn as [H1 H2]. exact (KB pn H1 H2). }
  assert (KR : forall x, gr <= x < gr + 8 \/ gr + 912 <= x < gr + 960 -> mbyte segs mem' x = mbyte segs mem x)
    by (intros x Hx; apply KG; unfold REC_SIZE; lia).
  assert (KO : forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl' /\
            forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)).
  { intros pn Hpn. apply KB'. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply app].
    apply in_or_app. right. exact Hpn. }
  destruct (rep_rest_keep segs bl bl' mem mem' gr R (l_answer Q) (l_reply Q) HA HP HX KR KO) as (RA & RP & RX).
  unfold rep_at, g1_calls, g1_own.
  cbn [set_spill r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host
       l_calls l_spill l_answer l_reply fst snd].
  split; [exact (g1_storage_keep segs mem mem' gr sc HS KW)|].
  split.
  - refine (conj C1 (conj C2 (conj _ (conj _ (conj _ (Forall_nil _)))))).
    + apply (bytes_at_keep_in segs mem mem' gr (gr + REC_SIZE));
        [exact C3 | unfold OFF_NCALLS; lia | rewrite length_le4; unfold OFF_NCALLS, REC_SIZE; lia | exact KG].
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (call_at_keep segs bl bl' mem mem'); [exact Hc | |].
      * intros x Hx. apply KG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
      * intros pn Hpn. apply KB'. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply in_or_app. left.
        apply in_concat. exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + unfold call_at. cbn [fst snd length]. split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
      split; [exact BF|]. split; [exact BA|]. split; [constructor|]. intros k s pn Es. destruct k; discriminate.
  - split; [exact RA|]. split; [exact RP|]. split; [exact RX|]. split.
    + unfold lay_blocks in *. cbn [l_calls l_spill l_answer l_reply]. exact (nodup_fst_drop_mid _ _ _ HND).
    + intros pn Hpn. apply HAP. apply (lay_drop_spill Q pn HND) in Hpn. exact (proj1 Hpn).
Qed.

Lemma call_at_arg : forall bl bl' mem mem' e fn As P x p k,
  call_at segs bl mem e (fn, As) P -> (length As < 6)%nat ->
  bytes_at segs mem' (e + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
  bytes_at segs mem' (e + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) (le8 (Z_to_bv 64 p)) ->
  (forall a, e <= a < e + CALL_SIZE -> ~ (e + CALL_OFF_NARGS <= a < e + CALL_OFF_NARGS + 4) ->
     ~ (e + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a < e + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
     mbyte segs mem' a = mbyte segs mem a) ->
  (forall pn, In pn P -> In pn bl' /\
     forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)) ->
  ~ In p (map fst P) -> p <> 0 -> In (p, k) bl' -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
  bytes_at segs mem' p (x ++ [Z_to_bv 8 0]) -> no0 x ->
  call_at segs bl' mem' e (fn, As ++ [x]) (P ++ [(p, k)]).
Proof.
  intros bl bl' mem mem' e fn As P x p k (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk) H6 BN BS K KP Hfr Hp0 Hin Hsz Hx Hno.
  cbn [fst snd] in *.
  unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  unfold call_at. cbn [fst snd]. unfold CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS.
  split; [exact Hfn|]. split; [rewrite length_app; cbn [length]; lia|].
  split; [rewrite !length_app, Hl; reflexivity|].
  split; [apply (bytes_at_keep_in segs mem mem' e (e + 4));
          [exact Hb0 | lia | rewrite length_le4; lia | intros a Ha; apply K; lia]|].
  split; [rewrite length_app, Nat2Z.inj_add; exact BN|].
  split; [exact (nodup_fst_snoc P p k Hnd Hfr)|].
  intros j s pn Es Ep.
  destruct (Nat.lt_ge_cases j (length As)) as [Hj|Hj].
  - rewrite nth_error_app1 in Es by exact Hj. rewrite nth_error_app1 in Ep by (rewrite Hl; exact Hj).
    destruct (Hk j s pn Es Ep) as (Hs & Hq0 & Hq & Hqs & Hstr & Hno').
    assert (Hpn : In pn P) by (eapply nth_error_In; exact Ep).
    destruct (KP pn Hpn) as [Kin Kp].
    split; [apply (bytes_at_keep_in segs mem mem' (e + 8 + 8 * Z.of_nat j) (e + 8 + 8 * Z.of_nat j + 8));
            [exact Hs | lia | rewrite length_le8; lia | intros a Ha; apply K; lia]|].
    split; [exact Hq0|]. split; [exact Kin|]. split; [exact Hqs|]. split; [|exact Hno'].
    apply (bytes_at_keep segs mem); [exact Hstr|]. intros i Hi. apply Kp.
    rewrite length_app in Hi. cbn [length] in Hi. lia.
  - destruct (Nat.eq_dec j (length As)) as [->|Hne].
    + rewrite nth_error_app2, Nat.sub_diag in Es by lia. cbn in Es. injection Es as <-.
      rewrite nth_error_app2 in Ep by (rewrite Hl; lia). rewrite Hl, Nat.sub_diag in Ep. cbn in Ep.
      injection Ep as <-.
      cbn [fst snd]. split; [exact BS|]. split; [exact Hp0|]. split; [exact Hin|]. split; [exact Hsz|].
      split; [exact Hx | exact Hno].
    + exfalso. assert (N : nth_error (As ++ [x]) j = None)
        by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
      rewrite N in Es. discriminate.
Qed.

Lemma rep_at_arg_lt : forall gr sc bl bl' mem mem' R fn As l0 P S ans rep x p k,
  rep_at segs bl mem gr sc (set_calls R (r_calls R ++ [(fn, As)])) (RLay (l0 ++ [P]) S ans rep) ->
  (length (r_calls R) < 16)%nat -> (length As < 6)%nat ->
  bytes_at segs mem' (gr + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_NARGS)
    (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
  bytes_at segs mem' (gr + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_ARGS + 8 * Z.of_nat (length As))
    (le8 (Z_to_bv 64 p)) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE ->
     ~ (gr + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_NARGS <= a <
        gr + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_NARGS + 4) ->
     ~ (gr + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
        gr + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
     mbyte segs mem' a = mbyte segs mem a) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs mem a -> writable_at segs mem' a) ->
  (forall pn, In pn (lay_blocks (RLay (l0 ++ [P]) S ans rep)) -> In pn bl' /\
     forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)) ->
  ~ In p (map fst (lay_blocks (RLay (l0 ++ [P]) S ans rep))) -> p <> 0 -> In (p, k) bl' ->
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
  bytes_at segs mem' p (x ++ [Z_to_bv 8 0]) ->
  iv_apart p k gr REC_SIZE -> iv_apart p k sc SC_SIZE ->
  rep_at segs bl' mem' gr sc (set_calls R (r_calls R ++ [(fn, As ++ [x])])) (RLay (l0 ++ [P ++ [(p, k)]]) S ans rep).
Proof.
  intros gr sc bl bl' mem mem' R fn As l0 P S ans rep x p k HR Hn H6 BN BS KG KW KB Hfr Hp0 Hin Hno Hlx Hsz Hx Ha1 Ha2.
  destruct HR as (HS & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  destruct HW as [HND HAP].
  pose proof HS as (S1 & S2 & S3 & S4 & S5).
  cbn [set_calls r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host
       l_calls l_spill l_answer l_reply] in *.
  assert (MB : forall pn, In pn P -> In pn (lay_blocks (RLay (l0 ++ [P]) S ans rep))).
  { intros pn Hpn. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply in_or_app. left.
    rewrite concat_app. apply in_or_app. right. cbn [concat]. rewrite app_nil_r. exact Hpn. }
  assert (KP : forall pn, In pn P -> In pn bl' /\
            forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i))
    by (intros pn Hpn; apply KB; apply MB; exact Hpn).
  assert (HfrP : ~ In p (map fst P)).
  { intros Hq. apply Hfr. apply in_map_iff in Hq as (pn & E & Hq). apply in_map_iff. exists pn.
    split; [exact E | apply MB; exact Hq]. }
  assert (L0 : length l0 = length (r_calls R)) by (rewrite !length_app in C2; cbn [length] in C2; lia).
  assert (Ee : nth_error (r_calls R ++ [(fn, As)]) (length (r_calls R)) = Some (fn, As))
    by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
  assert (Ep : nth_error (l0 ++ [P]) (length (r_calls R)) = Some P)
    by (rewrite nth_error_app2, L0, Nat.sub_diag by lia; reflexivity).
  destruct (C4 _ _ _ Ee Ep) as [CE CL].
  assert (KR : forall a, gr <= a < gr + 8 \/ gr + 912 <= a < gr + 960 -> mbyte segs mem' a = mbyte segs mem a).
  { intros a Ha. apply KG; unfold REC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS; [left; lia | lia | lia]. }
  assert (KO : forall pn, In pn (oblk ans ++ oblk rep) -> In pn bl' /\
            forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)).
  { intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    apply in_or_app. right. apply in_or_app. right. exact Hpn. }
  destruct (rep_rest_keep segs bl bl' mem mem' gr R ans rep HA HP HX KR KO) as (RA & RP & RX).
  unfold rep_at, g1_calls, g1_own.
  cbn [set_calls r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
  split; [exact (g1_storage_keep segs mem mem' gr sc HS KW)|].
  unfold iv_apart, OFF_CALLS, OFF_NCALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS, REC_SIZE, SC_SIZE in *.
  split.
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ C6))))).
    + rewrite length_app in *. cbn [length] in *. lia.
    + rewrite !length_app. cbn [length]. lia.
    + rewrite length_app in *. cbn [length] in *.
      apply (bytes_at_keep_in segs mem mem' (gr + 8) (gr + 12));
        [exact C3 | lia | rewrite length_le4; lia | intros a Ha; apply KG; [left; lia | lia | lia]].
    + intros i c P' Ec EP'.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      * assert (Ec0 : nth_error (r_calls R ++ [(fn, As)]) i = Some c)
          by (rewrite nth_error_app1 in Ec |- * by exact Hi; exact Ec).
        assert (EP0 : nth_error (l0 ++ [P]) i = Some P')
          by (rewrite nth_error_app1 in EP' |- * by lia; exact EP').
        destruct (C4 i c P' Ec0 EP0) as [Hc HL]. split; [|exact HL].
        apply (call_at_keep segs bl bl' mem mem'); [exact Hc | |].
        -- intros a Ha. unfold CALL_SIZE in Ha. apply KG; [left; lia | lia | lia].
        -- intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
           apply in_or_app. left. apply in_concat. exists P'. split; [eapply nth_error_In; exact EP0 | exact Hpn].
      * destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
        -- rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
           rewrite nth_error_app2, L0, Nat.sub_diag in EP' by lia. cbn in EP'. injection EP' as <-.
           split; [|apply Forall_app; split; [exact CL | constructor; [exact Hlx | constructor]]].
           apply (call_at_arg bl bl' mem mem' _ fn As P x p k CE H6);
             [exact BN | exact BS | | exact KP | exact HfrP | exact Hp0 | exact Hin | exact Hsz | exact Hx | exact Hno].
           intros a Ha H1 H2. unfold CALL_SIZE in Ha. apply KG; [left; lia | exact H1 | exact H2].
        -- exfalso. assert (N : nth_error (r_calls R ++ [(fn, As ++ [x])]) i = None)
             by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
           rewrite N in Ec. discriminate.
    + apply (call_at_keep segs bl bl' mem mem'); [exact C5 | |].
      * intros a Ha. unfold CALL_SIZE in Ha. apply KG; [right; lia | lia | lia].
      * intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
        apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - split; [exact RA|]. split; [exact RP|]. split; [exact RX|].
    pose proof (lay_perm_lt l0 P S ans rep (p, k)) as PERM.
    split.
    + apply (nodup_fst_perm _ _ (Permutation_sym PERM)). apply nodup_fst_snoc; [exact HND | exact Hfr].
    + intros pn Hpn. apply (Permutation_in _ PERM) in Hpn. apply in_app_or in Hpn as [Hpn|[<-|[]]];
        [exact (HAP pn Hpn)|]. cbn [fst snd]. split; assumption.
Qed.

Lemma rep_at_arg_full : forall gr sc bl bl' mem mem' R fn As lc S ans rep x p k,
  rep_at segs bl mem gr sc (set_spill R (fn, As)) (RLay lc S ans rep) ->
  (length As < 6)%nat ->
  bytes_at segs mem' (sc + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
  bytes_at segs mem' (sc + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) (le8 (Z_to_bv 64 p)) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE ->
     ~ (sc + CALL_OFF_NARGS <= a < sc + CALL_OFF_NARGS + 4) ->
     ~ (sc + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a < sc + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
     mbyte segs mem' a = mbyte segs mem a) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs mem a -> writable_at segs mem' a) ->
  (forall pn, In pn (lay_blocks (RLay lc S ans rep)) -> In pn bl' /\
     forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)) ->
  ~ In p (map fst (lay_blocks (RLay lc S ans rep))) -> p <> 0 -> In (p, k) bl' ->
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
  bytes_at segs mem' p (x ++ [Z_to_bv 8 0]) ->
  iv_apart p k gr REC_SIZE -> iv_apart p k sc SC_SIZE ->
  rep_at segs bl' mem' gr sc (set_spill R (fn, As ++ [x])) (RLay lc (S ++ [(p, k)]) ans rep).
Proof.
  intros gr sc bl bl' mem mem' R fn As lc S ans rep x p k HR H6 BN BS KG KW KB Hfr Hp0 Hin Hno Hlx Hsz Hx Ha1 Ha2.
  destruct HR as (HS & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  destruct HW as [HND HAP].
  pose proof HS as (S1 & S2 & S3 & S4 & S5).
  cbn [set_spill r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host
       l_calls l_spill l_answer l_reply fst snd] in *.
  assert (MB : forall pn, In pn S -> In pn (lay_blocks (RLay lc S ans rep))).
  { intros pn Hpn. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply in_or_app. right.
    apply in_or_app. left. exact Hpn. }
  assert (KP : forall pn, In pn S -> In pn bl' /\
            forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i))
    by (intros pn Hpn; apply KB; apply MB; exact Hpn).
  assert (HfrP : ~ In p (map fst S)).
  { intros Hq. apply Hfr. apply in_map_iff in Hq as (pn & E & Hq). apply in_map_iff. exists pn.
    split; [exact E | apply MB; exact Hq]. }
  assert (KR : forall a, gr <= a < gr + 8 \/ gr + 912 <= a < gr + 960 -> mbyte segs mem' a = mbyte segs mem a).
  { intros a Ha. unfold iv_apart, REC_SIZE, SC_SIZE in S3.
    apply KG; unfold REC_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS; [left; lia | lia | lia]. }
  assert (KO : forall pn, In pn (oblk ans ++ oblk rep) -> In pn bl' /\
            forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)).
  { intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    apply in_or_app. right. apply in_or_app. right. exact Hpn. }
  destruct (rep_rest_keep segs bl bl' mem mem' gr R ans rep HA HP HX KR KO) as (RA & RP & RX).
  unfold rep_at, g1_calls, g1_own.
  cbn [set_spill r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply fst snd].
  split; [exact (g1_storage_keep segs mem mem' gr sc HS KW)|].
  unfold iv_apart, OFF_CALLS, OFF_NCALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS, REC_SIZE, SC_SIZE in *.
  split.
  - refine (conj C1 (conj C2 (conj _ (conj _ (conj _ _))))).
    + apply (bytes_at_keep_in segs mem mem' (gr + 8) (gr + 12));
        [exact C3 | lia | rewrite length_le4; lia | intros a Ha; apply KG; [left; lia | lia | lia]].
    + intros i c P' Ec EP'. destruct (C4 i c P' Ec EP') as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (call_at_keep segs bl bl' mem mem'); [exact Hc | |].
      * intros a Ha. unfold CALL_SIZE in Ha. apply KG; [left; lia | lia | lia].
      * intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
        apply in_or_app. left. apply in_concat. exists P'. split; [eapply nth_error_In; exact EP' | exact Hpn].
    + apply (call_at_arg bl bl' mem mem' sc fn As S x p k C5 H6);
        [exact BN | exact BS | | exact KP | exact HfrP | exact Hp0 | exact Hin | exact Hsz | exact Hx | exact Hno].
      intros a Ha H1 H2. unfold CALL_SIZE in Ha. apply KG; [right; lia | exact H1 | exact H2].
    + apply Forall_app. split; [exact C6 | constructor; [exact Hlx | constructor]].
  - split; [exact RA|]. split; [exact RP|]. split; [exact RX|].
    pose proof (lay_perm_full lc S ans rep (p, k)) as PERM.
    split.
    + apply (nodup_fst_perm _ _ (Permutation_sym PERM)). apply nodup_fst_snoc; [exact HND | exact Hfr].
    + intros pn Hpn. apply (Permutation_in _ PERM) in Hpn. apply in_app_or in Hpn as [Hpn|[<-|[]]];
        [exact (HAP pn Hpn)|]. cbn [fst snd]. split; assumption.
Qed.

Lemma rec_rep_arg : forall gr sc L A mem L' A' mem' R fn As O x p k,
  rec_rep segs gr sc L A mem (rec_record R fn As) O ->
  (length As < 6)%nat ->
  bytes_at segs mem' (rec_entry gr sc R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
  bytes_at segs mem' (rec_entry gr sc R + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) (le8 (Z_to_bv 64 p)) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE ->
     ~ (rec_entry gr sc R + CALL_OFF_NARGS <= a < rec_entry gr sc R + CALL_OFF_NARGS + 4) ->
     ~ (rec_entry gr sc R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
        rec_entry gr sc R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
     mbyte segs mem' a = mbyte segs mem a) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs mem a -> writable_at segs mem' a) ->
  (forall pn, In pn O -> In pn (blocks L' A') /\
     forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)) ->
  ~ In p (map fst O) -> p <> 0 -> In (p, k) (blocks L' A') ->
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
  bytes_at segs mem' p (x ++ [Z_to_bv 8 0]) ->
  iv_apart p k gr REC_SIZE -> iv_apart p k sc SC_SIZE ->
  rec_rep segs gr sc L' A' mem' (rec_record R fn (As ++ [x])) (O ++ [(p, k)]).
Proof.
  intros gr sc L A mem L' A' mem' R fn As O x p k (Q & HR & HO) H6 BN BS KG KW KB Hfr Hp0 Hin Hno Hlx Hsz Hx Ha1 Ha2.
  assert (KB' : forall pn, In pn (lay_blocks Q) -> In pn (blocks L' A') /\
            forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i))
    by (intros pn Hpn; apply KB; apply HO; exact Hpn).
  assert (Hfr' : ~ In p (map fst (lay_blocks Q))).
  { intros Hq. apply Hfr. apply in_map_iff in Hq as (pn & E & Hq). apply in_map_iff. exists pn.
    split; [exact E | apply HO; exact Hq]. }
  destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hn|Hn].
  - rewrite (rec_entry_lt gr sc R Hn) in BN, BS, KG.
    rewrite (rec_record_lt R fn As Hn) in HR. rewrite (rec_record_lt R fn (As ++ [x]) Hn).
    destruct Q as [lc ls la lr].
    pose proof HR as (_ & (_ & C2 & _) & _).
    cbn [set_calls r_calls l_calls] in C2. rewrite length_app in C2. cbn [length] in C2.
    assert (NE : lc <> []) by (intros E; rewrite E in C2; cbn in C2; lia).
    destruct (exists_last NE) as (l0 & P & E). subst lc.
    exists (RLay (l0 ++ [P ++ [(p, k)]]) ls la lr). split.
    + exact (rep_at_arg_lt gr sc (blocks L A) (blocks L' A') mem mem' R fn As l0 P ls la lr x p k
               HR Hn H6 BN BS KG KW KB' Hfr' Hp0 Hin Hno Hlx Hsz Hx Ha1 Ha2).
    + exact (lay_perm_iff O _ _ (p, k) HO (lay_perm_lt l0 P ls la lr (p, k))).
  - assert (ER : forall Bs, rec_record R fn Bs = set_spill R (fn, Bs)).
    { intros Bs. unfold rec_record. destruct (Nat.ltb_spec (length (r_calls R)) 16); [lia | reflexivity]. }
    assert (Hn16 : length (r_calls R) = 16%nat).
    { pose proof HR as (_ & (C1 & _) & _). rewrite ER in C1. cbn [set_spill r_calls] in C1. lia. }
    rewrite (rec_entry_full gr sc R Hn16) in BN, BS, KG.
    rewrite ER in HR. rewrite ER.
    destruct Q as [lc ls la lr].
    exists (RLay lc (ls ++ [(p, k)]) la lr). split.
    + exact (rep_at_arg_full gr sc (blocks L A) (blocks L' A') mem mem' R fn As lc ls la lr x p k
               HR H6 BN BS KG KW KB' Hfr' Hp0 Hin Hno Hlx Hsz Hx Ha1 Ha2).
    + exact (lay_perm_iff O _ _ (p, k) HO (lay_perm_full lc ls la lr (p, k))).
Qed.

Lemma rep_at_set_word : forall bl mem mem' gr sc R R' Q,
  rep_at segs bl mem gr sc R Q ->
  r_calls R' = r_calls R -> r_spill R' = r_spill R -> r_answer R' = r_answer R -> r_reply R' = r_reply R ->
  (forall a, gr <= a < gr + 944 \/ sc <= a < sc + SC_SIZE -> mbyte segs mem' a = mbyte segs mem a) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs mem a -> writable_at segs mem' a) ->
  (forall pn, In pn (lay_blocks Q) ->
     forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)) ->
  g1_scalars segs mem' gr R' ->
  rep_at segs bl mem' gr sc R' Q.
Proof.
  intros bl mem mem' gr sc R R' Q HR E1 E2 E3 E4 KG KW KB HX'.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn bl /\
            forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i))
    by (intros pn Hpn; split; [exact (rep_at_blocks segs bl mem gr sc R Q pn HR Hpn) | exact (KB pn Hpn)]).
  destruct HR as (HS & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold rep_at, g1_calls. rewrite E1, E2, E3, E4.
  split; [exact (g1_storage_keep segs mem mem' gr sc HS KW)|].
  split.
  - refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (bytes_at_keep_in segs mem mem' (gr + OFF_NCALLS) (gr + OFF_NCALLS + 4));
        [exact C3 | lia | rewrite length_le4; lia | intros a Ha; apply KG; unfold OFF_NCALLS in Ha; left; lia].
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (call_at_keep segs bl bl mem mem'); [exact Hc | |].
      * intros a Ha. apply KG. left. unfold OFF_CALLS, CALL_SIZE in *. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + apply (call_at_keep segs bl bl mem mem'); [exact C5 | intros a Ha; apply KG; right; unfold CALL_SIZE, SC_SIZE in *; lia |].
      intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - assert (KO : forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl /\
              forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)).
    { intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
    destruct (ans_rep_keep segs bl bl mem mem' gr R (l_answer Q) (l_reply Q) HA HP
                ltac:(intros x Hx; apply KG; left; lia) KO) as [RA RP].
    split; [exact RA|]. split; [exact RP|]. split; [exact HX' | exact HW].
Qed.

Lemma rec_rep_set_state : forall gr sc L A mem mem' R O h,
  rec_rep segs gr sc L A mem R O -> 0 <= h < 2 ^ 64 ->
  bytes_at segs mem' (gr + OFF_STATE) (le8 (Z_to_bv 64 h)) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> ~ (gr + OFF_STATE <= a < gr + OFF_STATE + 8) ->
     mbyte segs mem' a = mbyte segs mem a) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs mem a -> writable_at segs mem' a) ->
  (forall p k i, In (p, k) O -> 0 <= i < k -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) ->
  rec_rep segs gr sc L A mem' (set_state R h) O.
Proof.
  intros gr sc L A mem mem' R O h (Q & HR & HO) Hh BS KG KW KB.
  exists Q. split; [|exact HO].
  pose proof HR as ((_ & _ & S3 & _ & _) & _ & _ & _ & HX & _).
  unfold iv_apart, REC_SIZE, SC_SIZE in S3.
  apply (rep_at_set_word (blocks L A) mem mem' gr sc R (set_state R h) Q HR eq_refl eq_refl eq_refl eq_refl).
  - intros a Ha. apply KG; unfold REC_SIZE, SC_SIZE, OFF_STATE in *; lia.
  - exact KW.
  - intros [p k] Hpn i Hi. exact (KB p k i (proj2 (HO (p, k)) Hpn) Hi).
  - unfold g1_scalars in *. cbn [set_state r_refuse r_code r_nreplies r_state r_host].
    unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, REC_SIZE in *.
    destruct HX as (X1 & X2 & X3 & X4 & X5 & R1 & R2 & R3 & R4 & R5).
    refine (conj _ (conj _ (conj _ (conj BS (conj _ (conj R1 (conj R2 (conj R3 (conj Hh R5))))))))).
    + apply (bytes_at_keep_in segs mem mem' gr (gr + 4));
        [exact X1 | lia | rewrite length_le4; lia | intros x Hx; apply KG; lia].
    + apply (bytes_at_keep_in segs mem mem' (gr + 4) (gr + 8));
        [exact X2 | lia | rewrite length_le4; lia | intros x Hx; apply KG; lia].
    + apply (bytes_at_keep_in segs mem mem' (gr + 920) (gr + 924));
        [exact X3 | lia | rewrite length_le4; lia | intros x Hx; apply KG; lia].
    + apply (bytes_at_keep_in segs mem mem' (gr + 952) (gr + 960));
        [exact X5 | lia | rewrite length_le8; lia | intros x Hx; apply KG; lia].
Qed.

Lemma rec_rep_set_host : forall gr sc L A mem mem' R O h,
  rec_rep segs gr sc L A mem R O -> 0 <= h < 2 ^ 64 ->
  bytes_at segs mem' (gr + OFF_HOST) (le8 (Z_to_bv 64 h)) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> ~ (gr + OFF_HOST <= a < gr + OFF_HOST + 8) ->
     mbyte segs mem' a = mbyte segs mem a) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs mem a -> writable_at segs mem' a) ->
  (forall p k i, In (p, k) O -> 0 <= i < k -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) ->
  rec_rep segs gr sc L A mem' (set_host R h) O.
Proof.
  intros gr sc L A mem mem' R O h (Q & HR & HO) Hh BS KG KW KB.
  exists Q. split; [|exact HO].
  pose proof HR as ((_ & _ & S3 & _ & _) & _ & _ & _ & HX & _).
  unfold iv_apart, REC_SIZE, SC_SIZE in S3.
  apply (rep_at_set_word (blocks L A) mem mem' gr sc R (set_host R h) Q HR eq_refl eq_refl eq_refl eq_refl).
  - intros a Ha. apply KG; unfold REC_SIZE, SC_SIZE, OFF_HOST in *; lia.
  - exact KW.
  - intros [p k] Hpn i Hi. exact (KB p k i (proj2 (HO (p, k)) Hpn) Hi).
  - unfold g1_scalars in *. cbn [set_host r_refuse r_code r_nreplies r_state r_host].
    unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, REC_SIZE in *.
    destruct HX as (X1 & X2 & X3 & X4 & X5 & R1 & R2 & R3 & R4 & R5).
    refine (conj _ (conj _ (conj _ (conj _ (conj BS (conj R1 (conj R2 (conj R3 (conj R4 Hh))))))))).
    + apply (bytes_at_keep_in segs mem mem' gr (gr + 4));
        [exact X1 | lia | rewrite length_le4; lia | intros x Hx; apply KG; lia].
    + apply (bytes_at_keep_in segs mem mem' (gr + 4) (gr + 8));
        [exact X2 | lia | rewrite length_le4; lia | intros x Hx; apply KG; lia].
    + apply (bytes_at_keep_in segs mem mem' (gr + 920) (gr + 924));
        [exact X3 | lia | rewrite length_le4; lia | intros x Hx; apply KG; lia].
    + apply (bytes_at_keep_in segs mem mem' (gr + 944) (gr + 952));
        [exact X4 | lia | rewrite length_le8; lia | intros x Hx; apply KG; lia].
Qed.

End Step2.

Lemma ans_entry_record : forall R fn As, (length (r_calls R) <= 16)%nat ->
  answer_c.ans_entry (rec_record R fn As) (rec_entry G_REC REC_SC R) (fn, As).
Proof.
  intros R fn As H. unfold answer_c.ans_entry.
  destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hl|Hg].
  - left. exists (length (r_calls R)). rewrite (rec_record_lt R fn As Hl), (rec_entry_lt G_REC REC_SC R Hl).
    cbn [set_calls r_calls]. split; [rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | reflexivity].
  - right. assert (E : length (r_calls R) = 16%nat) by lia.
    rewrite (rec_record_full R fn As E), (rec_entry_full G_REC REC_SC R E). split; reflexivity.
Qed.
