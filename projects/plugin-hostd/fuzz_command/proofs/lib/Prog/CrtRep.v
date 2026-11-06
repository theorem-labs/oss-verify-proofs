From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP.
Import ListNotations.
Local Open Scope Z_scope.

Section R.
Variable segs : list Segment.

Lemma rep_call_pn : forall bl mem a c P pn, call_at segs bl mem a c P -> In pn P -> In pn bl /\ 1 <= snd pn.
Proof.
  intros bl mem a c P pn (_ & _ & HL & _ & _ & _ & HK) Hin.
  apply In_nth_error in Hin as (k & Ek).
  assert (Hk : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (HK k s pn Es Ek) as (_ & _ & Hb & Hsz & _). split; [exact Hb | lia].
Qed.

Lemma rep_O : forall L A m R O pn, g_rec_rep segs L A m R O -> In pn O -> In pn (blocks L A) /\ 1 <= snd pn.
Proof.
  intros L A m R O pn (Q & (HS & HC & HA & HP & HX & HW) & HO) Hin.
  apply HO in Hin. unfold lay_blocks in Hin.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP' & Hpn).
    apply In_nth_error in HP' as (i & Ei).
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    exact (rep_call_pn _ _ _ _ _ _ (proj1 (C4 i c P Ec Ei)) Hpn).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (rep_call_pn _ _ _ _ _ _ C5 Hin)|].
    apply in_app_or in Hin as [Hin|Hin].
    + unfold answer_at in HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [q|];
        cbn [oblk In] in Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HA as (_ & _ & Hb & Hsz & _). split; [exact Hb | lia].
    + unfold reply_at in HP. destruct (r_reply R) as [t|]; destruct (l_reply Q) as [q|];
        cbn [oblk In] in Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HP as (_ & _ & _ & Hne & Hb & Hsz & _).
      split; [exact Hb|]. destruct t as [|b0 t]; [contradiction|]. cbn [length] in Hsz. lia.
Qed.

Lemma rep_O_apart : forall L A m R O p n, g_rec_rep segs L A m R O -> In (p, n) O ->
  p + n <= G_REC \/ G_REC + REC_SIZE <= p.
Proof.
  intros L A m R O p n (Q & (_ & _ & _ & _ & _ & _ & HW) & HO) Hin.
  apply HO in Hin. destruct (HW _ Hin) as [H _]. unfold iv_apart in H. cbn [fst snd] in H. exact H.
Qed.

Lemma rep_ncalls : forall L A m R O, g_rec_rep segs L A m R O ->
  bytes_at segs m 212304 (le4 (Z_to_bv 64 (Z.of_nat (length (r_calls R))))) /\
  (length (r_calls R) <= 16)%nat /\
  (forall c, In c (r_calls R) -> (length (snd c) <= 6)%nat /\ Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)).
Proof.
  intros L A m R O (Q & (_ & HC & _) & _). destruct HC as (C1 & C2 & C3 & C4 & _).
  split; [exact C3|]. split; [exact C1|].
  intros c Hc. apply In_nth_error in Hc as (i & Ec).
  assert (Hi : (i < length (l_calls Q))%nat) by (rewrite C2; apply nth_error_Some; rewrite Ec; discriminate).
  destruct (nth_error (l_calls Q) i) as [P|] eqn:EP; [|apply nth_error_None in EP; lia].
  destruct (C4 i c P Ec EP) as [(_ & H & _) HF]. split; [exact H | exact HF].
Qed.

Lemma rep_scal : forall L A m R O, g_rec_rep segs L A m R O ->
  bytes_at segs m 213240 (le8 (Z_to_bv 64 (r_state R))) /\ bytes_at segs m 213248 (le8 (Z_to_bv 64 (r_host R))) /\
  0 <= r_state R < 2 ^ 64 /\ 0 <= r_host R < 2 ^ 64.
Proof.
  intros L A m R O (Q & (_ & _ & _ & _ & HX & _) & _). destruct HX as (_ & _ & _ & X4 & X5 & _ & _ & _ & X9 & X10).
  split; [exact X4|]. split; [exact X5|]. split; [exact X9 | exact X10].
Qed.

Lemma rep_sh : forall L A m R O, g_rec_rep segs L A m R O ->
  rw_cells segs m 213240 [C8 (Z_to_bv 64 (r_state R)); C8 (Z_to_bv 64 (r_host R))].
Proof.
  intros L A m R O H. pose proof H as (Q & ((_ & _ & _ & HW1 & _) & _) & _).
  destruct (rep_scal L A m R O H) as (S1 & S2 & _).
  split; [split; [cbn; tauto|]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact S1|].
    rewrite length_le8. exact S2.
  - destruct HW1 as (W0 & W1 & W2). unfold G_REC, REC_SIZE in *. cbn [cells_size csize].
    split; [lia|]. split; [lia|]. intros i Hi.
    replace (213240 + i) with (212296 + (944 + i)) by lia. apply W2. lia.
Qed.

Lemma rep_set_sh : forall L A m m' R O sb hb, g_rec_rep segs L A m R O ->
  (forall p n, In (p, n) O -> 0 <= p /\ p + n <= 2 ^ 64) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (213240 <= x < 213256) -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, writable_at segs m x -> writable_at segs m' x) ->
  bytes_at segs m' 213240 (le8 (Z_to_bv 64 sb)) -> bytes_at segs m' 213248 (le8 (Z_to_bv 64 hb)) ->
  0 <= sb < 2 ^ 64 -> 0 <= hb < 2 ^ 64 ->
  g_rec_rep segs L A m' (set_host (set_state R sb) hb) O.
Proof.
  intros L A m m' R O sb hb REP ORNG KX KW BS BH RS RH.
  pose proof REP as (Q & HR & HO).
  exists Q. split; [|exact HO].
  unfold rep_at, g1_storage, g1_calls, g1_scalars, g1_own, answer_at, reply_at in *.
  cbn [set_host set_state r_refuse r_code r_calls r_spill r_answer r_nreplies r_reply r_state r_host].
  destruct HR as (HS & HC & HA & HP & HX & HW).
  assert (KB : forall a bs, bytes_at segs m a bs -> a + Z.of_nat (length bs) <= 213240 \/ 213256 <= a ->
             bytes_at segs m' a bs).
  { intros a bs Hb Ha. pose proof (bytes_at_bound segs m a bs Hb) as Hr.
    apply (bytes_at_keep segs m); [exact Hb|]. intros i Hi. apply KX; lia. }
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (blocks L A) /\
     forall i, 0 <= i < snd pn -> mbyte segs m' (fst pn + i) = mbyte segs m (fst pn + i)).
  { intros [p n] Hpn. pose proof Hpn as Hpn'. apply HO in Hpn'.
    destruct (rep_O L A m R O (p, n) REP Hpn') as [Hb _]. split; [exact Hb|].
    intros i Hi. destruct (proj2 HW _ Hpn) as [Ha _]. unfold iv_apart, G_REC, REC_SIZE in Ha. cbn [fst snd] in *.
    destruct (ORNG p n Hpn'). apply KX; lia. }
  assert (KG : forall x, 212296 <= x < 213240 -> mbyte segs m' x = mbyte segs m x) by (intros x Hx; apply KX; lia).
  assert (KS : forall x, 212240 <= x < 212296 -> mbyte segs m' x = mbyte segs m x) by (intros x Hx; apply KX; lia).
  unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, OFF_REFUSE, OFF_CODE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_NREPLIES,
    OFF_REPLY, OFF_REPLY_SIZE, OFF_STATE, OFF_HOST, CALL_SIZE in *.
  split; [| split; [| split; [| split]]].
  - destruct HS as (H1 & H2 & H3 & H4 & H5). refine (conj H1 (conj H2 (conj H3 (conj _ _)))).
    + apply (wr_at_keep segs m); [exact H4|]. intros i Hi Hw. exact (KW _ Hw).
    + apply (wr_at_keep segs m); [exact H5|]. intros i Hi Hw. exact (KW _ Hw).
  - destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply KB; [exact C3 | rewrite length_le4; lia].
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hil : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (call_at_keep segs (blocks L A) (blocks L A) m m'); [exact Hc | |].
      * intros x Hx. apply KG. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + apply (call_at_keep segs (blocks L A) (blocks L A) m m'); [exact C5 | |].
      * intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - revert HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [[p n]|] eqn:EA; intros HA; try contradiction.
    + destruct HA as (N1 & N2 & N3 & N4 & N5 & N6 & N7). cbn [fst snd] in *.
      assert (Hq : In (p, n) (lay_blocks Q)).
      { unfold lay_blocks. rewrite EA. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
        left. reflexivity. }
      destruct (KQ (p, n) Hq) as [Kin Kp]. cbn [fst snd] in Kp.
      split; [apply KB; [exact N1 | rewrite length_le8; lia]|].
      split; [exact N2|]. split; [exact Kin|]. split; [exact N4|].
      split; [|split; [exact N6 | exact N7]].
      apply (bytes_at_keep segs m); [exact N5|]. intros i Hi. apply Kp. rewrite length_app in Hi. cbn [length] in Hi. lia.
    + apply KB; [exact HA | rewrite length_le8; lia].
  - revert HP. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [[p n]|] eqn:EP; intros HP; try contradiction.
    + destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). cbn [fst snd] in *.
      assert (Hq : In (p, n) (lay_blocks Q)).
      { unfold lay_blocks. rewrite EP. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
        left. reflexivity. }
      destruct (KQ (p, n) Hq) as [Kin Kp]. cbn [fst snd] in Kp.
      split; [apply KB; [exact P1 | rewrite length_le8; lia]|].
      split; [apply KB; [exact P2 | rewrite length_le8; lia]|].
      split; [exact P3|]. split; [exact P4|]. split; [exact Kin|]. split; [exact P6|].
      split; [|exact P8].
      apply (bytes_at_keep segs m); [exact P7|]. intros i Hi. apply Kp. lia.
    + destruct HP as [P1 P2].
      split; [apply KB; [exact P1 | rewrite length_le8; lia]|].
      apply KB; [exact P2 | rewrite length_le8; lia].
  - split; [|exact HW].
    destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
    refine (conj _ (conj _ (conj _ (conj BS (conj BH (conj X6 (conj X7 (conj X8 (conj RS RH)))))))));
      (apply KB; [first [exact X1 | exact X2 | exact X3] | rewrite length_le4; lia]).
Qed.

Lemma rep_reply : forall L A m R O x, g_rec_rep segs L A m R O -> r_reply R = Some x ->
  exists p n, bytes_at segs m 213224 (le8 (Z_to_bv 64 p)) /\ p <> 0 /\ In (p, n) O /\ In (p, n) (blocks L A) /\
    Z.of_nat (length x) <= n /\ bytes_at segs m p x /\ Z.of_nat (length x) <= LMAX + 2.
Proof.
  intros L A m R O x (Q & (_ & _ & _ & HP & _) & HO) E. unfold reply_at in HP. rewrite E in HP.
  destruct (l_reply Q) as [[p n]|] eqn:EQ; [|contradiction].
  destruct HP as (P1 & _ & P3 & _ & P5 & P6 & P7 & P8). cbn [fst snd] in *.
  exists p, n. split; [exact P1|]. split; [exact P3|].
  split; [apply HO; unfold lay_blocks; rewrite EQ; apply in_or_app; right; apply in_or_app; right;
          apply in_or_app; right; left; reflexivity|].
  split; [exact P5|]. split; [exact (proj1 P6)|]. split; [exact P7 | exact P8].
Qed.

Lemma rep_calls : forall L A m R O, g_rec_rep segs L A m R O ->
  exists Ps, length Ps = length (r_calls R) /\
    forall i c P, nth_error (r_calls R) i = Some c -> nth_error Ps i = Some P ->
      call_at segs (blocks L A) m (212312 + 56 * Z.of_nat i) c P /\ (forall pn, In pn P -> In pn O).
Proof.
  intros L A m R O (Q & (_ & HC & _) & HO). destruct HC as (C1 & C2 & C3 & C4 & _).
  exists (l_calls Q). split; [exact C2|]. intros i c P Ec EP.
  destruct (C4 i c P Ec EP) as [Hc _]. split; [exact Hc|].
  intros pn Hpn. apply HO. unfold lay_blocks. apply in_or_app. left. apply in_concat.
  exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
Qed.

End R.
