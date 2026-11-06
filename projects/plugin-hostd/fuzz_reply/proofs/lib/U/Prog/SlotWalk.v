From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotParse SlotInv SlotSteps SlotHead.
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition sp_next (d : list Z) (k : Z) : Z := if k <? zlen d then fst (sp_pass d k) else k.

Lemma sp_pos_succ d f k0 : sp_pos d (S f) k0 = sp_next d (sp_pos d f k0).
Proof.
  revert k0. induction f as [|f IH]; intros k0; [reflexivity|].
  change (sp_pos d (S (S f)) k0) with (if k0 <? zlen d then sp_pos d (S f) (fst (sp_pass d k0)) else k0).
  change (sp_pos d (S f) k0) with (if k0 <? zlen d then sp_pos d f (fst (sp_pass d k0)) else k0).
  destruct (k0 <? zlen d) eqn:E.
  - apply IH.
  - unfold sp_next. rewrite E. reflexivity.
Qed.

Lemma walk_step pl t k : walk_at pl t k -> k < zlen (plz pl) -> walk_at pl (t + 1) (fst (sp_pass (plz pl) k)).
Proof.
  intros (Ht & ->) Hk. split; [lia|]. replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia.
  rewrite sp_pos_succ. unfold sp_next. rewrite (proj2 (Z.ltb_lt _ _) Hk). reflexivity.
Qed.

Lemma walk_chunk pl t k c : walk_at pl t k -> t < 512 -> k < zlen (plz pl) -> snd (sp_pass (plz pl) k) = Some c ->
  In c (pl_chunks pl).
Proof.
  intros (Ht & ->) Ht5 Hk Hs. rewrite pl_chunks_eq.
  assert (G : forall t0 f k0, (t0 < f)%nat -> sp_pos (plz pl) t0 k0 < zlen (plz pl) ->
            snd (sp_pass (plz pl) (sp_pos (plz pl) t0 k0)) = Some c -> In c (sp_walk (plz pl) f k0)).
  { intros t0. induction t0 as [|t0 IH]; intros f k0 Hf Hk0 Hs0.
    - destruct f as [|f]; [lia|]. cbn [sp_pos] in Hk0, Hs0. cbn [sp_walk].
      rewrite (proj2 (Z.ltb_lt _ _) Hk0), Hs0. exact (or_introl eq_refl).
    - destruct f as [|f]; [lia|]. cbn [sp_pos] in Hk0, Hs0. cbn [sp_walk]. revert Hk0 Hs0.
      destruct (Z.ltb_spec k0 (zlen (plz pl))) as [Lk|Lk]; intros Hk0 Hs0; cbv iota in Hk0, Hs0 |- *.
      + destruct (snd (sp_pass (plz pl) k0)); [right|]; apply IH; first [lia|assumption].
      + lia. }
  apply (G (Z.to_nat t) 512%nat 0); [lia|exact Hk|exact Hs].
Qed.

Lemma zlen_plz E : ss_n E = Z.of_nat (length (ss_pl E)) -> zlen (plz (ss_pl E)) = ss_n E.
Proof. intros H. unfold zlen, plz. rewrite length_map. lia. Qed.

Lemma sp_byte_plz pl k : sp_byte (plz pl) k = bv_unsigned (nth (Z.to_nat k) pl (Z_to_bv 8 0)).
Proof.
  unfold sp_byte, plz.
  transitivity (nth (Z.to_nat k) (map (fun b => bv_unsigned b) pl) (bv_unsigned (Z_to_bv 8 0)));
    [f_equal; vm_compute; reflexivity|].
  apply (map_nth (fun b => bv_unsigned b)).
Qed.

Lemma sp_op E k : sp_byte (plz (ss_pl E)) k mod 10 = op_at E k.
Proof. unfold op_at, in_byte. rewrite sp_byte_plz. reflexivity. Qed.

Lemma sp_in_byte E k : sp_byte (plz (ss_pl E)) k = in_byte E k.
Proof. unfold in_byte. apply sp_byte_plz. Qed.

Lemma sp_rd_next d k : snd (sp_rd d k) = if k <? zlen d then k + 1 else k.
Proof. unfold sp_rd. destruct (k <? zlen d); reflexivity. Qed.

Lemma sp_rd_in d k : k < zlen d -> sp_rd d k = (sp_byte d k, k + 1).
Proof. intros H. unfold sp_rd. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma sp_pass_op0 d k : sp_byte d k mod 10 = 0 -> sp_pass d k = (k + 1, None).
Proof. intros H. unfold sp_pass. rewrite H. reflexivity. Qed.

Lemma sp_pass_pick d k op : sp_byte d k mod 10 = op -> op = 2 \/ op = 3 \/ op = 4 \/ op = 6 ->
  sp_pass d k = (snd (sp_rd d (k + 1)), None).
Proof. intros H Hc. unfold sp_pass. rewrite H. destruct Hc as [-> | [-> | [-> | ->]]]; reflexivity. Qed.

Lemma sp_pass_one d k op : sp_byte d k mod 10 = op -> op = 5 \/ op = 8 \/ op = 9 ->
  sp_pass d k = (snd (sp_rd d (k + 1)), None).
Proof. intros H Hc. unfold sp_pass. rewrite H. destruct Hc as [-> | [-> | ->]]; reflexivity. Qed.

Lemma sp_pass_op1 d k : sp_byte d k mod 10 = 1 -> sp_pass d k = sp_take d 1 (snd (sp_rd d (k + 1))).
Proof. intros H. unfold sp_pass. rewrite H. reflexivity. Qed.

Lemma sp_pass_op7 d k : sp_byte d k mod 10 = 7 -> sp_pass d k = sp_take d 7 (k + 1).
Proof. intros H. unfold sp_pass. rewrite H. reflexivity. Qed.

Lemma sp_take_in d op j : j + 2 <= zlen d ->
  sp_take d op j =
  (j + 2 + Z.min (sp_byte d j + 256 * sp_byte d (j + 1)) (zlen d - (j + 2)),
   Some (CK op (j + 2) (firstn (Z.to_nat (Z.min (sp_byte d j + 256 * sp_byte d (j + 1)) (zlen d - (j + 2))))
     (skipn (Z.to_nat (j + 2)) d)))).
Proof.
  intros H. unfold sp_take. cbv zeta. rewrite (sp_rd_in d j) by lia. cbn [fst snd].
  rewrite (sp_rd_in d (j + 1)) by lia. cbn [fst snd]. replace (j + 1 + 1) with (j + 2) by lia. reflexivity.
Qed.

Lemma sp_take_short d op j : byte_ok d -> j <= zlen d < j + 2 -> fst (sp_take d op j) = zlen d.
Proof.
  intros Hok H. unfold sp_take. cbv zeta. cbn [fst].
  assert (K2 : snd (sp_rd d (snd (sp_rd d j))) = zlen d).
  { rewrite (sp_rd_next d j). destruct (Z.ltb_spec j (zlen d)) as [L1|L1]; cbv beta iota; rewrite sp_rd_next.
    - destruct (Z.ltb_spec (j + 1) (zlen d)); cbv beta iota; lia.
    - destruct (Z.ltb_spec j (zlen d)); cbv beta iota; lia. }
  rewrite K2. pose proof (sp_rd_ok d j Hok). pose proof (sp_rd_ok d (snd (sp_rd d j)) Hok). lia.
Qed.

Theorem walk_op0 E t k : walk_at (ss_pl E) t k -> ss_n E = Z.of_nat (length (ss_pl E)) -> k < ss_n E ->
  op_at E k = 0 -> walk_at (ss_pl E) (t + 1) (k + 1).
Proof.
  intros HW HN Hk Hop.
  assert (EQ : fst (sp_pass (plz (ss_pl E)) k) = k + 1).
  { rewrite sp_pass_op0; [reflexivity|]. rewrite sp_op. exact Hop. }
  rewrite <- EQ. apply walk_step; [exact HW|]. rewrite (zlen_plz E HN). exact Hk.
Qed.

Theorem walk_pick E t k op : walk_at (ss_pl E) t k -> ss_n E = Z.of_nat (length (ss_pl E)) -> k < ss_n E ->
  op_at E k = op -> op = 2 \/ op = 3 \/ op = 4 \/ op = 6 -> walk_at (ss_pl E) (t + 1) (disp_k E op k).
Proof.
  intros HW HN Hk Hop Hc.
  assert (Hb : sp_byte (plz (ss_pl E)) k mod 10 = op) by (rewrite sp_op; exact Hop).
  assert (Hp : pick_op op = true) by (destruct Hc as [-> | [-> | [-> | ->]]]; reflexivity).
  assert (EQ : fst (sp_pass (plz (ss_pl E)) k) = disp_k E op k).
  { rewrite (sp_pass_pick _ _ op Hb Hc). cbn [fst]. rewrite sp_rd_next, (zlen_plz E HN).
    unfold disp_k. rewrite Hp. cbn [andb]. destruct (k + 1 <? ss_n E); cbv beta iota; lia. }
  rewrite <- EQ. apply walk_step; [exact HW|]. rewrite (zlen_plz E HN). exact Hk.
Qed.

Theorem walk_one E t k op : walk_at (ss_pl E) t k -> ss_n E = Z.of_nat (length (ss_pl E)) -> k < ss_n E ->
  op_at E k = op -> op = 5 \/ op = 8 \/ op = 9 ->
  walk_at (ss_pl E) (t + 1) (if k + 1 <? ss_n E then k + 2 else k + 1).
Proof.
  intros HW HN Hk Hop Hc.
  assert (Hb : sp_byte (plz (ss_pl E)) k mod 10 = op) by (rewrite sp_op; exact Hop).
  assert (EQ : fst (sp_pass (plz (ss_pl E)) k) = if k + 1 <? ss_n E then k + 2 else k + 1).
  { rewrite (sp_pass_one _ _ op Hb Hc). cbn [fst]. rewrite sp_rd_next, (zlen_plz E HN).
    destruct (k + 1 <? ss_n E); cbv beta iota; lia. }
  rewrite <- EQ. apply walk_step; [exact HW|]. rewrite (zlen_plz E HN). exact Hk.
Qed.

Lemma walk_pass_take E k op j : ss_n E = Z.of_nat (length (ss_pl E)) -> op_at E k = op ->
  (op = 1 /\ j = disp_k E 1 k) \/ (op = 7 /\ j = k + 1) -> sp_pass (plz (ss_pl E)) k = sp_take (plz (ss_pl E)) op j.
Proof.
  intros HN Hop Hj. assert (Hb : sp_byte (plz (ss_pl E)) k mod 10 = op) by (rewrite sp_op; exact Hop).
  destruct Hj as [[-> ->]|[-> ->]].
  - rewrite (sp_pass_op1 _ _ Hb). f_equal. rewrite sp_rd_next, (zlen_plz E HN). unfold disp_k.
    replace (pick_op 1) with true by reflexivity. cbn [andb]. destruct (k + 1 <? ss_n E); cbv beta iota; lia.
  - exact (sp_pass_op7 _ _ Hb).
Qed.

Theorem walk_take E t k op j : walk_at (ss_pl E) t k -> ss_n E = Z.of_nat (length (ss_pl E)) -> k < ss_n E ->
  op_at E k = op -> (op = 1 /\ j = disp_k E 1 k) \/ (op = 7 /\ j = k + 1) -> j + 2 <= ss_n E ->
  walk_at (ss_pl E) (t + 1) (j + 2 + Z.min (in_byte E j + 256 * in_byte E (j + 1)) (ss_n E - (j + 2))) /\
  (t < 512 -> In (CK op (j + 2) (plz (firstn (Z.to_nat (Z.min (in_byte E j + 256 * in_byte E (j + 1))
                                                              (ss_n E - (j + 2))))
                                         (skipn (Z.to_nat (j + 2)) (ss_pl E))))) (pl_chunks (ss_pl E))).
Proof.
  intros HW HN Hk Hop Hj Hjn.
  pose proof (walk_pass_take E k op j HN Hop Hj) as EP.
  rewrite (sp_take_in _ op j ltac:(rewrite (zlen_plz E HN); exact Hjn)), !sp_in_byte, (zlen_plz E HN) in EP.
  assert (HkL : k < zlen (plz (ss_pl E))) by (rewrite (zlen_plz E HN); exact Hk).
  split.
  - pose proof (walk_step (ss_pl E) t k HW HkL) as W. rewrite EP in W. exact W.
  - intros Ht. apply (walk_chunk (ss_pl E) t k _ HW Ht HkL). rewrite EP. cbn [snd]. f_equal. f_equal.
    unfold plz. rewrite skipn_map, firstn_map. reflexivity.
Qed.

Theorem walk_take_short E t k op j : walk_at (ss_pl E) t k -> ss_n E = Z.of_nat (length (ss_pl E)) -> k < ss_n E ->
  op_at E k = op -> (op = 1 /\ j = disp_k E 1 k) \/ (op = 7 /\ j = k + 1) -> j <= ss_n E < j + 2 ->
  walk_at (ss_pl E) (t + 1) (ss_n E).
Proof.
  intros HW HN Hk Hop Hj Hjn.
  pose proof (walk_pass_take E k op j HN Hop Hj) as EP.
  assert (HkL : k < zlen (plz (ss_pl E))) by (rewrite (zlen_plz E HN); exact Hk).
  pose proof (walk_step (ss_pl E) t k HW HkL) as W. rewrite EP, sp_take_short, (zlen_plz E HN) in W; [exact W| |].
  - apply plz_ok.
  - rewrite (zlen_plz E HN). exact Hjn.
Qed.

Lemma frame_len : forall B API LS SH SK ra empty rc fx j E CS,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> ss_n E = Z.of_nat (length (ss_pl E)).
Proof. intros B API LS SH SK ra empty rc fx j E CS (_ & _ & ((_ & LEN & _) & _) & _). exact LEN. Qed.

Definition take_end (E : sstart) (j : Z) : Z :=
  if j + 2 <=? ss_n E then j + 2 + Z.min (in_byte E j + 256 * in_byte E (j + 1)) (ss_n E - (j + 2)) else ss_n E.

Theorem walk_take_end E t k op j : walk_at (ss_pl E) t k -> ss_n E = Z.of_nat (length (ss_pl E)) -> k < ss_n E ->
  op_at E k = op -> (op = 1 /\ j = disp_k E 1 k) \/ (op = 7 /\ j = k + 1) -> j <= ss_n E ->
  walk_at (ss_pl E) (t + 1) (take_end E j).
Proof.
  intros HW HN Hk Hop Hj Hjn. unfold take_end. destruct (Z.leb_spec (j + 2) (ss_n E)) as [L|L].
  - exact (proj1 (walk_take E t k op j HW HN Hk Hop Hj L)).
  - exact (walk_take_short E t k op j HW HN Hk Hop Hj ltac:(lia)).
Qed.

Theorem walk_op1 E t k : walk_at (ss_pl E) t k -> ss_n E = Z.of_nat (length (ss_pl E)) -> k < ss_n E ->
  op_at E k = 1 -> walk_at (ss_pl E) (t + 1) (take_end E (disp_k E 1 k)).
Proof.
  intros HW HN Hk Hop. apply (walk_take_end E t k 1); [exact HW|exact HN|exact Hk|exact Hop|left; split; reflexivity|].
  unfold disp_k. destruct (pick_op 1 && (k + 1 <? ss_n E)) eqn:C; [|lia].
  apply andb_true_iff in C as [_ C]. apply Z.ltb_lt in C. lia.
Qed.

Theorem walk_op7 E t k : walk_at (ss_pl E) t k -> ss_n E = Z.of_nat (length (ss_pl E)) -> k < ss_n E ->
  op_at E k = 7 -> walk_at (ss_pl E) (t + 1) (take_end E (k + 1)).
Proof.
  intros HW HN Hk Hop. apply (walk_take_end E t k 7); [exact HW|exact HN|exact Hk|exact Hop|right; split; reflexivity|lia].
Qed.

Lemma pick_not1 op : pick_op op = true -> op <> 1 -> op = 2 \/ op = 3 \/ op = 4 \/ op = 6.
Proof.
  unfold pick_op. intros H N.
  apply orb_true_iff in H as [H|H]; [|apply Z.eqb_eq in H; right; right; right; exact H].
  apply orb_true_iff in H as [H|H]; [|apply Z.eqb_eq in H; right; right; left; exact H].
  apply orb_true_iff in H as [H|H]; [|apply Z.eqb_eq in H; right; left; exact H].
  apply orb_true_iff in H as [H|H]; [|apply Z.eqb_eq in H; left; exact H].
  apply Z.eqb_eq in H. contradiction.
Qed.
