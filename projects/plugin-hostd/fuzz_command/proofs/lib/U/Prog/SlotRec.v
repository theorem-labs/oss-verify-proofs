From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YM05 YO0i YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU Slot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_c joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require rec_shape_of_c check_arity_c VerbsB atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma mrd_mb : forall segs m a, Mem.mrd segs m (Mem.wa a) = mbyte segs m a.
Proof. reflexivity. Qed.

Definition wchk (a : Z) : bool :=
  match wview rsegs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end.

Definition pchk (a : Z) : bool :=
  match mbyte rsegs (fun _ => None) a with Some _ => true | None => false end.

Lemma wchk_ok : forall (m : word -> option byte) a, wchk a = true -> writable_at rsegs m a.
Proof.
  intros m a H.
  assert (H' : wview rsegs (fun _ => None) (Z_to_bv 64 a) <> None).
  { unfold wchk in H. destruct (wview rsegs (fun _ => None) (Z_to_bv 64 a)); [discriminate | discriminate H]. }
  unfold writable_at, wview in *. destruct (m (Z_to_bv 64 a)); [discriminate | exact H'].
Qed.

Lemma pchk_ok : forall (m : word -> option byte) a, pchk a = true -> mbyte rsegs m a <> None.
Proof.
  intros m a H.
  assert (H' : mbyte rsegs (fun _ => None) a <> None).
  { unfold pchk in H. destruct (mbyte rsegs (fun _ => None) a); [discriminate | discriminate H]. }
  unfold mbyte in *. destruct (m (Z_to_bv 64 a)); [discriminate | exact H'].
Qed.

Lemma g_wchk : forallb (fun i => wchk (0x33ff0 + i)) (map Z.of_nat (seq 0 1020)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma g_pchk : forallb (fun i => pchk (0x33ff0 + i)) (map Z.of_nat (seq 0 1020)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma g_writable : forall (m : word -> option byte) a, 0x33ff0 <= a < 0x343ec -> writable_at rsegs m a.
Proof.
  intros m a Ha. apply wchk_ok.
  pose proof (zseq_forall _ 1020 g_wchk (a - 0x33ff0) ltac:(lia)) as H.
  cbv beta in H. replace (0x33ff0 + (a - 0x33ff0)) with a in H by lia. exact H.
Qed.

Lemma g_present : forall (m : word -> option byte) a, 0x33ff0 <= a < 0x343ec -> mbyte rsegs m a <> None.
Proof.
  intros m a Ha. apply pchk_ok.
  pose proof (zseq_forall _ 1020 g_pchk (a - 0x33ff0) ltac:(lia)) as H.
  cbv beta in H. replace (0x33ff0 + (a - 0x33ff0)) with a in H by lia. exact H.
Qed.

Lemma guard_wchk : forallb (fun i => wchk (0x54730 + i)) (map Z.of_nat (seq 0 8)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma got_guard_wchk : forallb (fun i => wchk (0x22d40 + i)) (map Z.of_nat (seq 0 8)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma guard_writable : forall (m : word -> option byte) i, 0 <= i < 8 -> writable_at rsegs m (0x54730 + i).
Proof. intros m i Hi. apply wchk_ok. exact (zseq_forall _ 8 guard_wchk i ltac:(lia)). Qed.

Lemma got_guard_writable : forall (m : word -> option byte) i, 0 <= i < 8 -> writable_at rsegs m (0x22d40 + i).
Proof. intros m i Hi. apply wchk_ok. exact (zseq_forall _ 8 got_guard_wchk i ltac:(lia)). Qed.

Lemma g_wr_at : forall m a n, 0x33ff0 <= a -> a + n <= 0x343ec -> Mem.wr_at rsegs m a n.
Proof.
  intros m a n H1 H2. split; [lia|]. split; [lia|]. intros i Hi. exact (g_writable m (a + i) ltac:(lia)).
Qed.

Lemma le4_0 : Mem.le4 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 4.
Proof. apply StrFun.map_unsigned_inj. vm_compute. reflexivity. Qed.

Lemma le8_0 : Mem.le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. apply StrFun.map_unsigned_inj. vm_compute. reflexivity. Qed.

Lemma zero_bytes : forall m a n b len, zero_at m a n -> a <= b -> 0 <= a ->
  b + Z.of_nat len <= a + n -> b + Z.of_nat len <= 2 ^ 64 ->
  Mem.bytes_at rsegs m b (repeat (Z_to_bv 8 0) len).
Proof.
  intros m a n b len H Hab Ha Hb H64. split; [lia|]. split; [rewrite repeat_length; lia|].
  intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi. rewrite mrd_mb.
  replace (b + Z.of_nat i) with (a + (b - a + Z.of_nat i)) by lia. apply H. lia.
Qed.

Lemma zero_of : forall m a len, Mem.bytes_at rsegs m a (repeat (Z_to_bv 8 0) len) -> zero_at m a (Z.of_nat len).
Proof.
  intros m a len (_ & _ & H) i Hi. rewrite <- (Z2Nat.id i) by lia. rewrite <- mrd_mb.
  rewrite H by (rewrite repeat_length; lia). apply nth_error_repeat. lia.
Qed.

Lemma zero_at_join : forall m a n1 n2, zero_at m a n1 -> zero_at m (a + n1) n2 -> zero_at m a (n1 + n2).
Proof.
  intros m a n1 n2 H1 H2 i Hi. destruct (Z.lt_ge_cases i n1).
  - apply H1. lia.
  - replace (a + i) with (a + n1 + (i - n1)) by lia. apply H2. lia.
Qed.

Lemma bytes_exist : forall m a n, (forall i, 0 <= i < Z.of_nat n -> mbyte rsegs m (a + i) <> None) ->
  exists bs, length bs = n /\ forall i, (i < n)%nat -> mbyte rsegs m (a + Z.of_nat i) = nth_error bs i.
Proof.
  intros m a n. induction n as [|n IH]; intros H.
  - exists []. split; [reflexivity|]. intros i Hi. lia.
  - destruct IH as (bs & Hl & Hb). { intros i Hi. apply H. lia. }
    destruct (mbyte rsegs m (a + Z.of_nat n)) as [b|] eqn:E.
    2:{ exfalso. exact (H (Z.of_nat n) ltac:(lia) E). }
    exists (bs ++ [b]). split; [rewrite length_app, Hl; cbn [length]; lia|].
    intros i Hi. destruct (Nat.lt_ge_cases i n) as [Lt|Ge].
    + rewrite nth_error_app1 by lia. apply Hb. exact Lt.
    + assert (i = n) by lia. subst i. rewrite nth_error_app2 by lia. rewrite Hl, Nat.sub_diag. exact E.
Qed.

Lemma word4_g : forall m a, 0x33ff0 <= a -> a + 4 <= 0x343ec ->
  exists v, -2^31 <= v < 2^31 /\ Mem.bytes_at rsegs m a (Mem.le4 (Z_to_bv 64 v)).
Proof.
  intros m a H1 H2.
  destruct (bytes_exist m a 4) as (bs & Hl & Hb).
  { intros i Hi. apply g_present. lia. }
  pose proof (bytes_le_to_Z_bound bs) as Hz1. pose proof (bytes_le_to_Z_nonneg bs) as Hz0.
  rewrite Hl in Hz1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hz1.
  set (z := bytes_le_to_Z bs) in *.
  set (v := if z <? 2 ^ 31 then z else z - 2 ^ 32).
  assert (Hv : -2^31 <= v < 2^31 /\ v mod 2 ^ 32 = z).
  { unfold v. destruct (Z.ltb_spec z (2 ^ 31)).
    - split; [lia|]. apply Z.mod_small. lia.
    - split; [lia|]. replace (z - 2 ^ 32) with (z + (-1) * 2 ^ 32) by ring.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  exists v. split; [exact (proj1 Hv)|].
  assert (E : Mem.le4 (Z_to_bv 64 v) = bs).
  { unfold Mem.le4. rewrite Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2 ^ 64).
    rewrite (Mem.Z_to_le_bytes_mod 4 v 64) by lia.
    rewrite <- (Mem.Z_to_le_bytes_mod 4 v 32) by lia. rewrite (proj2 Hv).
    rewrite <- Hl. apply StrFun.Z_to_le_bytes_to_Z. }
  rewrite E. split; [lia|]. split; [rewrite Hl; lia|].
  intros i Hi. rewrite mrd_mb. apply Hb. rewrite Hl in Hi. exact Hi.
Qed.

Lemma word8_g : forall m a, 0x33ff0 <= a -> a + 8 <= 0x343ec ->
  exists v, 0 <= v < 2^64 /\ Mem.bytes_at rsegs m a (Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros m a H1 H2.
  destruct (bytes_exist m a 8) as (bs & Hl & Hb).
  { intros i Hi. apply g_present. lia. }
  pose proof (bytes_le_to_Z_bound bs) as Hz1. pose proof (bytes_le_to_Z_nonneg bs) as Hz0.
  rewrite Hl in Hz1. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hz1.
  set (z := bytes_le_to_Z bs) in *.
  exists z. split; [lia|].
  assert (E : Mem.le8 (Z_to_bv 64 z) = bs).
  { rewrite <- Mem.store_bytes_8. change (width_bytes 64) with 8%nat.
    rewrite Z_to_bv_unsigned. change (bv_wrap 64 z) with (z mod 2 ^ 64). rewrite Z.mod_small by lia.
    rewrite <- Hl. apply StrFun.Z_to_le_bytes_to_Z. }
  rewrite E. split; [lia|]. split; [rewrite Hl; lia|].
  intros i Hi. rewrite mrd_mb. apply Hb. rewrite Hl in Hi. exact Hi.
Qed.

Lemma call_at_empty : forall segs bl mem a, Mem.bytes_at segs mem a (repeat (Z_to_bv 8 0) 8) ->
  call_at segs bl mem a (0, []) [].
Proof.
  intros segs bl mem a H.
  change (repeat (Z_to_bv 8 0) 8) with (repeat (Z_to_bv 8 0) 4 ++ repeat (Z_to_bv 8 0) 4) in H.
  apply Mem.bytes_at_app in H as [H1 H2]. rewrite repeat_length in H2.
  unfold call_at, CALL_OFF_FN, CALL_OFF_NARGS. cbn [fst snd length].
  split; [unfold REC_FN_COUNT; lia|]. split; [lia|]. split; [reflexivity|].
  split; [rewrite Z.add_0_r, le4_0; exact H1|].
  split; [change (Z.of_nat 0) with 0; rewrite le4_0; exact H2|].
  split; [constructor|].
  intros k s pn Es. destruct k; discriminate.
Qed.

Lemma gi_rep : forall j L A mem, GI_cmd j mem -> exists R, g_rec_rep rsegs L A mem R [] /\ r_calls R = [] /\
  r_answer R = None /\ r_reply R = None /\ r_nreplies R = 0 /\ r_spill R = (0, []).
Proof.
  intros j L A mem (Z1 & Z2 & Z3 & Z4 & Z5).
  unfold G_REC_A, G_SPILL in *.
  destruct (word4_g mem (G_REC + OFF_REFUSE) ltac:(unfold G_REC, OFF_REFUSE; lia)
    ltac:(unfold G_REC, OFF_REFUSE; lia)) as (rf & Hrf & Brf).
  destruct (word4_g mem (G_REC + OFF_CODE) ltac:(unfold G_REC, OFF_CODE; lia)
    ltac:(unfold G_REC, OFF_CODE; lia)) as (cd & Hcd & Bcd).
  destruct (word8_g mem (G_REC + OFF_STATE) ltac:(unfold G_REC, OFF_STATE; lia)
    ltac:(unfold G_REC, OFF_STATE; lia)) as (st & Hst & Bst).
  destruct (word8_g mem (G_REC + OFF_HOST) ltac:(unfold G_REC, OFF_HOST; lia)
    ltac:(unfold G_REC, OFF_HOST; lia)) as (hs & Hhs & Bhs).
  exists (RState rf cd [] (0, []) None 0 None st hs).
  split; [| split; [reflexivity | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
  unfold g_rec_rep, rec_rep. exists (RLay [] [] None None). split; [| intros pn; cbn; tauto].
  unfold rep_at, g1_storage, g1_calls, answer_at, reply_at, g1_scalars, g1_own.
  cbn [r_refuse r_code r_calls r_spill r_answer r_nreplies r_reply r_state r_host l_calls l_spill l_answer l_reply
    fst snd length].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - destruct g_rec_layout as (L1 & L2 & L3). refine (conj L1 (conj L2 (conj L3 (conj _ _)))); apply g_wr_at;
      unfold G_REC, REC_SC, REC_SIZE, SC_SIZE; lia.
  - refine (conj _ (conj eq_refl (conj _ (conj _ (conj _ (Forall_nil _)))))).
    + lia.
    + change (Z.of_nat 0) with 0. rewrite le4_0. apply (zero_bytes mem _ 4 _ 4 Z1); unfold G_REC, OFF_NCALLS; lia.
    + intros i c P Ec. destruct i; discriminate.
    + apply call_at_empty. apply (zero_bytes mem _ 8 _ 8 Z4); unfold REC_SC; lia.
  - rewrite le8_0. apply (zero_bytes mem _ 12 _ 8 Z2); unfold G_REC, OFF_ANSWER; lia.
  - rewrite le8_0. split.
    + apply (zero_bytes mem _ 16 _ 8 Z3); unfold G_REC, OFF_REPLY; lia.
    + apply (zero_bytes mem _ 16 _ 8 Z3); unfold G_REC, OFF_REPLY_SIZE; lia.
  - refine (conj Brf (conj Bcd (conj _ (conj Bst (conj Bhs _))))).
    + rewrite le4_0. apply (zero_bytes mem _ 12 _ 4 Z2); unfold G_REC, OFF_NREPLIES; lia.
    + repeat split; lia.
  - split; [cbn; constructor | intros pn Hpn; cbn in Hpn; destruct Hpn].
Qed.

Lemma bytes_zero_le4 : forall m a, Mem.bytes_at rsegs m a (Mem.le4 (Z_to_bv 64 0)) -> zero_at m a 4.
Proof. intros m a H. rewrite le4_0 in H. exact (zero_of m a 4 H). Qed.

Lemma bytes_zero_le8 : forall m a, Mem.bytes_at rsegs m a (Mem.le8 (Z_to_bv 64 0)) -> zero_at m a 8.
Proof. intros m a H. rewrite le8_0 in H. exact (zero_of m a 8 H). Qed.

Lemma rep_gi : forall j L A mem R O, g_rec_rep rsegs L A mem R O -> r_calls R = [] -> r_answer R = None ->
  r_reply R = None -> r_nreplies R = 0 -> r_spill R = (0, []) ->
  Mem.bytes_at rsegs mem 0x343e8 (Mem.le4 (Z_to_bv 64 0)) -> GI_cmd j mem.
Proof.
  intros j L A mem R O (Q & HR & HO) Hc Ha Hr Hn Hs Hq.
  destruct HR as (HS & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  rewrite Hc in C3. cbn [length] in C3. change (Z.of_nat 0) with 0 in C3.
  rewrite Hs in C5. destruct C5 as (_ & _ & _ & S1 & S2 & _). cbn [fst snd length] in S1, S2.
  change (Z.of_nat 0) with 0 in S2.
  unfold answer_at in HA. rewrite Ha in HA. destruct (l_answer Q) as [pn|]; [destruct HA|].
  unfold reply_at in HP. rewrite Hr in HP. destruct (l_reply Q) as [pn|]; [destruct HP|].
  destruct HP as [P1 P2].
  destruct HX as (_ & _ & X3 & _). rewrite Hn in X3.
  unfold GI_cmd, G_REC_A, G_SPILL, G_QUIT_A.
  unfold G_REC, REC_SC, OFF_NCALLS, OFF_ANSWER, OFF_NREPLIES, OFF_REPLY, OFF_REPLY_SIZE, CALL_OFF_FN,
    CALL_OFF_NARGS in *.
  split; [|split; [|split; [|split]]].
  - exact (bytes_zero_le4 _ _ C3).
  - change 12 with (8 + 4). apply zero_at_join; [exact (bytes_zero_le8 _ _ HA) | exact (bytes_zero_le4 _ _ X3)].
  - change 16 with (8 + 8). apply zero_at_join; [exact (bytes_zero_le8 _ _ P1) | exact (bytes_zero_le8 _ _ P2)].
  - change 8 with (4 + 4). apply zero_at_join.
    + rewrite Z.add_0_r in S1. exact (bytes_zero_le4 _ _ S1).
    + exact (bytes_zero_le4 _ _ S2).
  - exact (bytes_zero_le4 _ _ Hq).
Qed.

Lemma concat_len6 : forall (ls : list (list (Z * Z))),
  (forall i P, nth_error ls i = Some P -> (length P <= 6)%nat) -> (length (concat ls) <= 6 * length ls)%nat.
Proof.
  induction ls as [|P ls IH]; intros H; cbn [concat length]; [lia|].
  rewrite length_app. pose proof (H 0%nat P eq_refl) as H0.
  assert (H1 : (length (concat ls) <= 6 * length ls)%nat) by (apply IH; intros i P' E; exact (H (S i) P' E)).
  lia.
Qed.

Lemma oblk_len : forall q : option (Z * Z), (length (oblk q) <= 1)%nat.
Proof. intros [q|]; cbn; lia. Qed.

Lemma rep_dedup : forall segs L A mem R O, g_rec_rep segs L A mem R O ->
  exists O', (forall pn, In pn O' <-> In pn O) /\ (length O' <= 104)%nat /\ g_rec_rep segs L A mem R O'.
Proof.
  intros segs L A mem R O (Q & HR & HO).
  exists (lay_blocks Q). split; [intros pn; specialize (HO pn); tauto|].
  split.
  - destruct HR as (_ & (C1 & C2 & _ & C4 & C5 & _) & _).
    assert (Hc : (length (concat (l_calls Q)) <= 6 * length (l_calls Q))%nat).
    { apply concat_len6. intros i P EP.
      assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite EP; discriminate).
      destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
      destruct (C4 i c P Ec EP) as [(_ & Hn & Hl & _) _]. lia. }
    destruct C5 as (_ & Hn & Hl & _).
    unfold lay_blocks. rewrite !length_app.
    pose proof (oblk_len (l_answer Q)). pose proof (oblk_len (l_reply Q)). lia.
  - exists Q. split; [exact HR | intros pn; tauto].
Qed.

Lemma call_at_in : forall segs bl m a c P pn, call_at segs bl m a c P -> In pn P -> In pn bl.
Proof.
  intros segs bl m a c P pn (_ & _ & Hl & _ & _ & _ & Hk) Hin.
  destruct (In_nth_error P pn Hin) as [k Ek].
  destruct (nth_error (snd c) k) as [s|] eqn:Es.
  - exact (proj1 (proj2 (proj2 (Hk k s pn Es Ek)))).
  - exfalso. apply nth_error_None in Es.
    assert (k < length P)%nat by (apply nth_error_Some; rewrite Ek; discriminate). lia.
Qed.

Lemma call_at_keep_same : forall segs bl m m' a c P,
  call_at segs bl m a c P ->
  (forall x, a <= x < a + CALL_SIZE -> mbyte segs m' x = mbyte segs m x) ->
  (forall pn i, In pn P -> 0 <= i < snd pn -> mbyte segs m' (fst pn + i) = mbyte segs m (fst pn + i)) ->
  call_at segs bl m' a c P.
Proof.
  intros segs bl m m' a c P H K KP. apply (call_at_keep segs bl bl m m' a c P H K).
  intros pn Hpn. split; [exact (call_at_in segs bl m a c P pn H Hpn)|]. intros i Hi. exact (KP pn i Hpn Hi).
Qed.

Lemma rep_at_move : forall segs bl mem mem' gr sc R R' Q,
  rep_at segs bl mem gr sc R Q ->
  Mem.wr_at segs mem' gr REC_SIZE -> Mem.wr_at segs mem' sc SC_SIZE ->
  (forall a, gr + 8 <= a < gr + 944 \/ sc <= a < sc + SC_SIZE -> mbyte segs mem' a = mbyte segs mem a) ->
  (forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)) ->
  r_calls R' = r_calls R -> r_spill R' = r_spill R -> r_answer R' = r_answer R -> r_reply R' = r_reply R ->
  g1_scalars segs mem' gr R' ->
  rep_at segs bl mem' gr sc R' Q.
Proof.
  intros segs bl mem mem' gr sc R R' Q (HS & HC & HA & HP & HX & HW) W1 W2 KG KB E1 E2 E3 E4 HX'.
  assert (KM : forall x, gr + 8 <= x < gr + 944 -> mbyte segs mem' x = mbyte segs mem x)
    by (intros x Hx; apply KG; left; exact Hx).
  assert (KS : forall x, sc <= x < sc + SC_SIZE -> mbyte segs mem' x = mbyte segs mem x)
    by (intros x Hx; apply KG; right; exact Hx).
  unfold rep_at, g1_storage, g1_calls, answer_at, reply_at in *.
  unfold SC_SIZE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, CALL_SIZE in *.
  split; [| split; [| split; [| split; [| split]]]].
  - destruct HS as (H1 & H2 & H3 & _ & _). exact (conj H1 (conj H2 (conj H3 (conj W1 W2)))).
  - rewrite E1, E2. destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (bytes_at_keep_in segs mem mem' (gr + 8) (gr + 944)); [exact C3 | lia | rewrite Mem.length_le4; lia | exact KM].
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hil : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (call_at_keep_same segs bl mem mem' _ c P Hc).
      * intros x Hx. apply KM. unfold CALL_SIZE in Hx. lia.
      * intros pn k Hpn Hk. apply KB; [|exact Hk]. unfold lay_blocks. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + apply (call_at_keep_same segs bl mem mem' sc (r_spill R) (l_spill Q) C5).
      * intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
      * intros pn k Hpn Hk. apply KB; [|exact Hk]. unfold lay_blocks. apply in_or_app. right. apply in_or_app.
        left. exact Hpn.
  - rewrite E3. revert HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [[p n]|] eqn:EA; intros HA;
      try contradiction.
    + destruct HA as (N1 & N2 & N3 & N4 & N5 & N6 & N7). cbn [fst snd] in *.
      assert (Hq : In (p, n) (lay_blocks Q)).
      { unfold lay_blocks. rewrite EA. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
        left. reflexivity. }
      split; [apply (bytes_at_keep_in segs mem mem' (gr + 8) (gr + 944)); [exact N1 | lia | rewrite Mem.length_le8; lia | exact KM]|].
      split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [|split; [exact N6 | exact N7]].
      apply (bytes_at_keep segs mem); [exact N5|]. intros i Hi. apply (KB (p, n) i Hq).
      rewrite length_app in Hi. cbn [length] in Hi. cbn [snd]. lia.
    + apply (bytes_at_keep_in segs mem mem' (gr + 8) (gr + 944)); [exact HA | lia | rewrite Mem.length_le8; lia | exact KM].
  - rewrite E4. revert HP. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [[p n]|] eqn:EP; intros HP;
      try contradiction.
    + destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). cbn [fst snd] in *.
      assert (Hq : In (p, n) (lay_blocks Q)).
      { unfold lay_blocks. rewrite EP. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
        left. reflexivity. }
      split; [apply (bytes_at_keep_in segs mem mem' (gr + 8) (gr + 944)); [exact P1 | lia | rewrite Mem.length_le8; lia | exact KM]|].
      split; [apply (bytes_at_keep_in segs mem mem' (gr + 8) (gr + 944)); [exact P2 | lia | rewrite Mem.length_le8; lia | exact KM]|].
      split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|].
      split; [|exact P8].
      apply (bytes_at_keep segs mem); [exact P7|]. intros i Hi. apply (KB (p, n) i Hq). cbn [snd]. lia.
    + destruct HP as [P1 P2].
      split; [apply (bytes_at_keep_in segs mem mem' (gr + 8) (gr + 944)); [exact P1 | lia | rewrite Mem.length_le8; lia | exact KM]|].
      apply (bytes_at_keep_in segs mem mem' (gr + 8) (gr + 944)); [exact P2 | lia | rewrite Mem.length_le8; lia | exact KM].
  - exact HX'.
  - exact HW.
Qed.

Lemma rep_set_rc : forall L A mem mem' R O rf cd,
  g_rec_rep rsegs L A mem R O -> -2^31 <= rf < 2^31 -> -2^31 <= cd < 2^31 ->
  Mem.bytes_at rsegs mem' 0x34028 (Mem.le4 (Z_to_bv 64 rf)) ->
  Mem.bytes_at rsegs mem' (0x34028 + 4) (Mem.le4 (Z_to_bv 64 cd)) ->
  (forall a, ~ (0x34028 <= a < 0x34028 + 8) -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
  g_rec_rep rsegs L A mem'
    (RState rf cd (r_calls R) (r_spill R) (r_answer R) (r_nreplies R) (r_reply R) (r_state R) (r_host R)) O.
Proof.
  intros L A mem mem' R O rf cd (Q & HR & HO) Hrf Hcd B1 B2 K.
  exists Q. split; [|exact HO].
  assert (HR' := HR). destruct HR' as (_ & _ & _ & _ & (X1 & X2 & X3 & X4 & X5 & X6) & (_ & HW)).
  apply (rep_at_move rsegs (blocks L A) mem mem' G_REC REC_SC R _ Q HR).
  - apply g_wr_at; unfold G_REC, REC_SIZE; lia.
  - apply g_wr_at; unfold REC_SC, SC_SIZE; lia.
  - intros a Ha. apply K. unfold G_REC, REC_SC, SC_SIZE in Ha. lia.
  - intros pn i Hpn Hi. apply K. destruct (HW pn Hpn) as [Ha _]. unfold iv_apart, G_REC, REC_SIZE in Ha. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold g1_scalars. cbn [r_refuse r_code r_nreplies r_state r_host].
    unfold G_REC, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
    refine (conj _ (conj B2 (conj _ (conj _ (conj _ _))))).
    + rewrite Z.add_0_r. exact B1.
    + apply (bytes_at_keep_in rsegs mem mem' (0x34028 + 8) (0x34028 + 960)); [exact X3 | lia | rewrite Mem.length_le4; lia |].
      intros x Hx. apply K. lia.
    + apply (bytes_at_keep_in rsegs mem mem' (0x34028 + 8) (0x34028 + 960)); [exact X4 | lia | rewrite Mem.length_le8; lia |].
      intros x Hx. apply K. lia.
    + apply (bytes_at_keep_in rsegs mem mem' (0x34028 + 8) (0x34028 + 960)); [exact X5 | lia | rewrite Mem.length_le8; lia |].
      intros x Hx. apply K. lia.
    + destruct X6 as (Y1 & Y2 & Y3 & Y4 & Y5). repeat split; lia.
Qed.

Lemma rep_set_sh : forall L A mem mem' R O,
  g_rec_rep rsegs L A mem R O ->
  Mem.bytes_at rsegs mem' (0x34028 + 944) (Mem.le8 (Z_to_bv 64 0) ++ Mem.le8 (Z_to_bv 64 0)) ->
  (forall a, ~ (0x34028 + 944 <= a < 0x34028 + 960) -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
  g_rec_rep rsegs L A mem' (set_host (set_state R 0) 0) O.
Proof.
  intros L A mem mem' R O (Q & HR & HO) B K.
  exists Q. split; [|exact HO].
  assert (HR' := HR). destruct HR' as (_ & _ & _ & _ & (X1 & X2 & X3 & X4 & X5 & X6) & (_ & HW)).
  apply Mem.bytes_at_app in B as [B1 B2]. rewrite Mem.length_le8 in B2.
  apply (rep_at_move rsegs (blocks L A) mem mem' G_REC REC_SC R _ Q HR).
  - apply g_wr_at; unfold G_REC, REC_SIZE; lia.
  - apply g_wr_at; unfold REC_SC, SC_SIZE; lia.
  - intros a Ha. apply K. unfold G_REC, REC_SC, SC_SIZE in Ha. lia.
  - intros pn i Hpn Hi. apply K. destruct (HW pn Hpn) as [Ha _]. unfold iv_apart, G_REC, REC_SIZE in Ha. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold g1_scalars. cbn [set_host set_state r_refuse r_code r_nreplies r_state r_host].
    unfold G_REC, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
    refine (conj _ (conj _ (conj _ (conj B1 (conj _ _))))).
    + apply (bytes_at_keep_in rsegs mem mem' 0x34028 (0x34028 + 944)); [exact X1 | lia | rewrite Mem.length_le4; lia |].
      intros x Hx. apply K. lia.
    + apply (bytes_at_keep_in rsegs mem mem' 0x34028 (0x34028 + 944)); [exact X2 | lia | rewrite Mem.length_le4; lia |].
      intros x Hx. apply K. lia.
    + apply (bytes_at_keep_in rsegs mem mem' 0x34028 (0x34028 + 944)); [exact X3 | lia | rewrite Mem.length_le4; lia |].
      intros x Hx. apply K. lia.
    + replace (0x34028 + 952) with (0x34028 + 944 + Z.of_nat 8) by reflexivity. exact B2.
    + destruct X6 as (Y1 & Y2 & Y3 & Y4 & Y5). repeat split; lia.
Qed.

Definition kp (R0 : rstate) (n : nat) (R : rstate) : Prop :=
  r_refuse R = r_refuse R0 /\ r_code R = r_code R0 /\ r_spill R = r_spill R0 /\ (length (r_calls R) <= n)%nat.

Ltac kp_pair E :=
  match type of E with
  | ?t = ((?a, _), _) => replace a with (fst (fst t)) by (rewrite E; reflexivity)
  | ?t = (?a, _) => replace a with (fst t) by (rewrite E; reflexivity)
  end.

Lemma kp_weak : forall R0 n n' R, kp R0 n R -> (n <= n')%nat -> kp R0 n' R.
Proof. intros R0 n n' R (H1 & H2 & H3 & H4) Hn. unfold kp. repeat split; try assumption; lia. Qed.

Lemma kp_record : forall R0 n R fn A, kp R0 n R -> (n < 16)%nat -> kp R0 (S n) (rec_record R fn A).
Proof.
  intros R0 n R fn A (H1 & H2 & H3 & H4) Hn. unfold rec_record.
  destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L]; [|lia].
  unfold kp, set_calls. cbn [r_refuse r_code r_spill r_calls]. rewrite length_app. cbn [length].
  repeat split; try assumption; lia.
Qed.

Lemma kp_mix : forall R0 n R c, kp R0 n R -> kp R0 n (rec_mix R c).
Proof. intros R0 n R c H. exact H. Qed.

Lemma kp_mix_host : forall R0 n R c, kp R0 n R -> kp R0 n (rec_mix_host R c).
Proof. intros R0 n R c H. exact H. Qed.

Lemma kp_hand_back : forall R0 n R t, kp R0 n R -> kp R0 n (fst (hand_back R t)).
Proof. intros R0 n R t H. exact H. Qed.

Lemma kp_answer : forall R0 n R c s ch, kp R0 n R -> kp R0 n (fst (rec_answer R c s ch)).
Proof. intros R0 n R c s ch H. unfold rec_answer. destruct (r_refuse R =? 0); [destruct ch|]; exact H. Qed.

Lemma kp_answer_code : forall R0 n R k, kp R0 n R -> kp R0 n (fst (rec_answer_code R k)).
Proof. intros R0 n R k H. exact H. Qed.

Lemma kp_socket_send_m : forall R0 n R x, kp R0 n R -> kp R0 n (fst (socket_send_m R x)).
Proof. intros R0 n R x H. exact H. Qed.

Lemma kp_sup_resp_m : forall R0 n R k, kp R0 n R -> kp R0 n (fst (sup_resp_m R k)).
Proof. intros R0 n R k H. exact H. Qed.

Lemma kp_stub : forall R0 n R fn A s ch, kp R0 n R -> (n < 16)%nat -> kp R0 (S n) (fst (rec_stub R fn A s ch)).
Proof. intros R0 n R fn A s ch H Hn. unfold rec_stub. apply kp_answer. apply kp_record; assumption. Qed.

Lemma kp_stub_code : forall R0 n R fn A, kp R0 n R -> (n < 16)%nat -> kp R0 (S n) (fst (rec_stub_code R fn A)).
Proof.
  intros R0 n R fn A H Hn. unfold rec_stub_code. cbv zeta.
  destruct (r_refuse (rec_record R fn A) =? 0); apply kp_answer_code; [apply kp_mix|];
    apply kp_record; assumption.
Qed.

Lemma kp_stub_mix : forall R0 n R fn A, kp R0 n R -> (n < 16)%nat -> kp R0 (S n) (rec_stub_mix R fn A).
Proof. intros R0 n R fn A H Hn. unfold rec_stub_mix. apply kp_mix. apply kp_record; assumption. Qed.

Lemma kp_pins_set_m : forall R0 n R u f l v, kp R0 n R -> (n < 16)%nat -> kp R0 (S n) (fst (pins_set_m R u f l v)).
Proof. intros R0 n R u f l v H Hn. unfold pins_set_m. apply kp_stub_code; assumption. Qed.

Lemma kp_pins_clear_m : forall R0 n R u, kp R0 n R -> (n < 16)%nat -> kp R0 (S n) (fst (pins_clear_m R u)).
Proof. intros R0 n R u H Hn. unfold pins_clear_m. apply kp_stub_code; assumption. Qed.

Lemma kp_lv2 : forall R0 n R u, kp R0 n R -> (n < 16)%nat -> kp R0 (S n) (lv2_refusals_forget_m R u).
Proof. intros R0 n R u H Hn. unfold lv2_refusals_forget_m. apply kp_stub_mix; assumption. Qed.

Lemma kp_desc_add : forall R0 n R u, kp R0 n R -> (n < 16)%nat -> kp R0 (S n) (descriptors_add_m R u).
Proof. intros R0 n R u H Hn. unfold descriptors_add_m. apply kp_stub_mix; assumption. Qed.

Lemma kp_sup_add_m : forall R0 n R u i p q, kp R0 n R -> (n < 16)%nat -> kp R0 (S n) (fst (sup_add_m R u i p q)).
Proof.
  intros R0 n R u i p q H Hn. unfold sup_add_m. cbv zeta.
  destruct ((i <? 0) || (10000 <=? i)).
  - apply kp_hand_back. apply kp_record; assumption.
  - destruct (negb (r_refuse (rec_record R REC_ADD _) =? 0)).
    + apply kp_hand_back. apply kp_record; assumption.
    + apply kp_hand_back. apply kp_mix. apply kp_record; assumption.
Qed.

Lemma kp_sup_broadcast_m : forall R0 n R ln, kp R0 n R -> (n < 16)%nat -> kp R0 (S n) (fst (sup_broadcast_m R ln)).
Proof. intros R0 n R ln H Hn. unfold sup_broadcast_m. apply kp_stub; assumption. Qed.

Lemma kp_sup_host_setting_m : forall R0 n R ln tk, kp R0 n R -> (n < 16)%nat ->
  kp R0 (S n) (sup_host_setting_m R ln tk).
Proof.
  intros R0 n R ln tk H Hn. unfold sup_host_setting_m. cbv zeta. apply kp_mix_host. apply kp_record; assumption.
Qed.

Lemma kp_after_reply : forall R0 n R i v, kp R0 n R -> (n < 16)%nat -> kp R0 (S n) (sup_after_reply_m R i v).
Proof. intros R0 n R i v H Hn. unfold sup_after_reply_m. apply kp_record; assumption. Qed.

Lemma kp_call : forall R0 n R c, kp R0 n R -> (n < 16)%nat -> kp R0 (S n) (fst (VerbsRun.run_call R c)).
Proof.
  intros R0 n R c H Hn. destruct c; cbn [VerbsRun.run_call];
    first
      [ apply kp_sup_add_m; assumption
      | unfold descriptors_get_m, descriptors_panel_get_m, sup_remove_m, sup_remove_all_m,
          sup_worker_list_m, sup_instance_info_m, sup_reset_m, sup_quarantine_clear_m,
          sup_policy_set_m, sup_lv2_worker_set_m, sup_pool_config_m, sup_worker_env_m,
          sup_chain_m, sup_chain_clear_m, sup_pin_accept_m, sup_instance_verb_m, sup_call_m,
          sup_connect_m;
        apply kp_stub; assumption ].
Qed.

Lemma kp_pins_follow : forall R0 n R rc, kp R0 n R -> (n < 16)%nat -> kp R0 (S n) (fst (VerbsRun.pins_follow R rc)).
Proof.
  intros R0 n R rc H Hn. unfold VerbsRun.pins_follow. cbn [fst].
  destruct (rc =? 0); [apply kp_lv2; assumption | apply (kp_weak R0 n); [exact H | lia]].
Qed.

Lemma kp_step : forall rcode R0 n R s, kp R0 n R -> (n + 2 <= 16)%nat ->
  kp R0 (S (S n)) (fst (fst (VerbsRun.run_step rcode R s))).
Proof.
  intros rcode R0 n R s H Hn. destruct s; cbn [VerbsRun.run_step fst].
  - apply (kp_weak R0 n); [exact H | lia].
  - apply (kp_weak R0 (S n)); [apply kp_call; [exact H | lia] | lia].
  - match goal with |- context [sup_add_m R ?u ?i ?p ?q] => destruct (sup_add_m R u i p q) as [R1 x] eqn:E end.
    cbn [fst].
    destruct (0 <=? rcode x).
    + apply kp_desc_add; [|lia]. kp_pair E. apply kp_sup_add_m; [exact H | lia].
    + apply (kp_weak R0 (S n)); [|lia]. kp_pair E. apply kp_sup_add_m; [exact H | lia].
  - match goal with |- context [pins_set_m R ?u ?f ?l ?v] => destruct (pins_set_m R u f l v) as [R1 r] eqn:E end.
    cbn [fst]. apply kp_pins_follow; [|lia]. kp_pair E. apply kp_pins_set_m; [exact H | lia].
  - match goal with |- context [pins_clear_m R ?u] => destruct (pins_clear_m R u) as [R1 r] eqn:E end.
    cbn [fst]. apply kp_pins_follow; [|lia]. kp_pair E. apply kp_pins_clear_m; [exact H | lia].
  - apply (kp_weak R0 n); [exact H | lia].
  - match goal with |- context [sup_broadcast_m R ?l] => destruct (sup_broadcast_m R l) as [R1 x] eqn:E end.
    cbn [fst]. apply kp_sup_host_setting_m; [|lia]. kp_pair E. apply kp_sup_broadcast_m; [exact H | lia].
Qed.

Lemma kp_run : forall atoi rcode R0 R D, kp R0 0 R ->
  kp R0 3 (fst (fst (VerbsRun.run_receive atoi rcode R D))).
Proof.
  intros atoi rcode R0 R D H. unfold VerbsRun.run_receive.
  destruct (Verbs.receive atoi D) as [st af].
  destruct (VerbsRun.run_step rcode R st) as [[R1 x] q] eqn:E.
  cbn [fst].
  destruct af as [[i v]|].
  - apply kp_after_reply; [|lia]. apply kp_socket_send_m. kp_pair E. apply kp_step; [exact H | lia].
  - apply (kp_weak R0 2); [|lia]. apply kp_socket_send_m. kp_pair E. apply kp_step; [exact H | lia].
Qed.

Lemma vr_keep : forall R D, let '(R', _, _) := vr_run (rec_clear R) D in
  r_refuse R' = r_refuse R /\ r_code R' = r_code R /\ r_spill R' = r_spill R.
Proof.
  intros R D.
  assert (H : kp (rec_clear R) 3 (fst (fst (vr_run (rec_clear R) D)))).
  { unfold vr_run. apply kp_run. unfold kp. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    cbn. lia. }
  destruct (vr_run (rec_clear R) D) as [[R' x] q] eqn:E.
  try rewrite E in H. cbn [fst] in H. destruct H as (H1 & H2 & H3 & _).
  cbn [rec_clear r_refuse r_code r_spill] in H1, H2, H3. exact (conj H1 (conj H2 H3)).
Qed.

Lemma find0_upto0 : forall M,
  match StrFun.find_byte 0 M with Some i => i | None => length M end = length (Verbs.upto0 M).
Proof.
  unfold Verbs.upto0. induction M as [|b M IH]; [reflexivity|].
  cbn [StrFun.find_byte Verbs.upto].
  destruct (bv_unsigned b =? 0); [reflexivity|].
  destruct (StrFun.find_byte 0 M) as [i|] eqn:F; try rewrite F in IH; cbn; lia.
Qed.

Lemma strnlen_upto0 : forall M len, Z.of_nat (length M) = len ->
  StrFun.strnlen_res len M = Z.of_nat (length (Verbs.upto0 M)).
Proof.
  intros M len <-. unfold StrFun.strnlen_res. rewrite Nat2Z.id, firstn_all.
  rewrite <- find0_upto0. destruct (StrFun.find_byte 0 M); reflexivity.
Qed.

Lemma words_acc_count : forall l cur,
  (2 * length (Verbs.words_acc cur l) <= length l + 1 + match cur with [] => 0 | _ :: _ => 1 end)%nat.
Proof.
  induction l as [|b l IH]; intros cur.
  - destruct cur; cbn; lia.
  - cbn [Verbs.words_acc]. destruct (Verbs.is_sep b).
    + specialize (IH []). destruct cur as [|c cur]; cbn in IH |- *; lia.
    + specialize (IH (cur ++ [b])). destruct cur as [|c cur]; cbn in IH |- *; lia.
Qed.

Lemma words_count : forall l, (2 * length (Verbs.words l) <= length l + 1)%nat.
Proof.
  intros l. unfold Verbs.words. pose proof (words_acc_count l []) as H. cbv beta iota in H. lia.
Qed.

Lemma words_acc_need : forall l cur,
  join_need (Verbs.words_acc cur l) <= Z.of_nat (length l) + 1 + Z.of_nat (length cur).
Proof.
  unfold join_need. induction l as [|b l IH]; intros cur.
  - destruct cur as [|c cur]; cbn [Verbs.words_acc fold_right]; lia.
  - cbn [Verbs.words_acc]. destruct (Verbs.is_sep b).
    + specialize (IH []). destruct cur as [|c cur]; cbn [fold_right length] in IH |- *; lia.
    + specialize (IH (cur ++ [b])). rewrite length_app in IH. cbn [length] in IH |- *. lia.
Qed.

Lemma join_need_words : forall l, join_need (Verbs.words l) <= Z.of_nat (length l) + 1.
Proof.
  intros l. unfold Verbs.words. pose proof (words_acc_need l []) as H.
  change (Z.of_nat (length (@nil byte))) with 0 in H. lia.
Qed.

Lemma dropw_len : forall p l, (length (Verbs.dropw p l) <= length l)%nat.
Proof.
  intros p. induction l as [|b l IH]; cbn [Verbs.dropw]; [cbn; lia|].
  destruct (p b); cbn [length]; lia.
Qed.

Lemma line_len : forall M, (length (Verbs.line M) <= length (Verbs.upto0 M))%nat.
Proof.
  intros M. unfold Verbs.line, Verbs.trim. rewrite length_rev.
  eapply Nat.le_trans; [apply dropw_len|]. rewrite length_rev. lia.
Qed.

Fixpoint img_chk (a : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom rsegs (Z_to_bv 64 a) with
      | Some b' => (bv_unsigned b' =? bv_unsigned b) && img_chk (a + 1) bs'
      | None => false
      end
  end.

Lemma img_chk_ok : forall bs a, img_chk a bs = true ->
  forall i, (i < length bs)%nat -> seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction bs as [|b bs IH]; intros a H i Hi; cbn [length] in Hi; [lia|].
  cbn [img_chk] in H. destruct (seg_rom rsegs (Z_to_bv 64 a)) as [b'|] eqn:E; [|discriminate].
  apply andb_prop in H as [H1 H2]. destruct i as [|i].
  - cbn [nth_error]. rewrite Z.add_0_r, E. f_equal. apply bv_eq. apply Z.eqb_eq. exact H1.
  - cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply IH; [exact H2 | lia].
Qed.

Lemma relro_bytes : forall mem a bs,
  (forall x, in_globals frame_RELRO x -> mbyte rsegs mem x = seg_rom rsegs (Z_to_bv 64 x)) ->
  0x226b0 <= a -> a + Z.of_nat (length bs) <= 0x226b0 + 1680 -> img_chk a bs = true ->
  Mem.bytes_at rsegs mem a bs.
Proof.
  intros mem a bs H Ha Hl Hc. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite mrd_mb. rewrite H.
  - apply img_chk_ok; assumption.
  - exists 0x226b0, 1680. split; [left; reflexivity | lia].
Qed.

Ltac relro_tac H :=
  apply relro_bytes; [exact H | lia | apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity].

Lemma relro_img : forall mem,
  (forall a, in_globals frame_RELRO a -> mbyte rsegs mem a = seg_rom rsegs (Z_to_bv 64 a)) ->
  Mem.bytes_at rsegs mem 0x22cf8 (Mem.le8 (Z_to_bv 64 0x34028)) /\
  Mem.bytes_at rsegs mem 0x22d00 (Mem.le8 (Z_to_bv 64 0x10b80)) /\
  Mem.bytes_at rsegs mem 0x22d08 (Mem.le8 (Z_to_bv 64 0x10a98)) /\
  Mem.bytes_at rsegs mem 0x22d10 (Mem.le8 (Z_to_bv 64 0x343e8)) /\
  Mem.bytes_at rsegs mem rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes /\
  Mem.bytes_at rsegs mem check_arity_c.G_PARSED check_arity_c.g_parsed_bytes /\
  Mem.bytes_at rsegs mem VerbsB.IV_TABLE_B (concat (map (fun p => Mem.le8 (Z_to_bv 64 p)) VerbsB.iv_ptrs_b)) /\
  Mem.bytes_at rsegs mem VerbsB.INFO_TABLE VerbsB.info_bytes.
Proof.
  intros mem H.
  unfold rec_shape_of_c.G_SHAPES, check_arity_c.G_PARSED, VerbsB.IV_TABLE_B, VerbsB.INFO_TABLE.
  split; [relro_tac H|]. split; [relro_tac H|]. split; [relro_tac H|]. split; [relro_tac H|].
  split; [relro_tac H|]. split; [relro_tac H|]. split; [relro_tac H|].
  relro_tac H.
Qed.

Lemma codes_declared : forall k, (k < 58)%nat ->
  declared (nth k rec_codes 0) = true /\ -2^31 <= nth k rec_codes 0 < 2^31.
Proof.
  intros k Hk.
  assert (Hin : In (nth k rec_codes 0) rec_codes) by (apply nth_In; rewrite rec_codes_length; exact Hk).
  assert (D : declared (nth k rec_codes 0) = true).
  { unfold declared. apply existsb_exists. exists (nth k rec_codes 0). split; [exact Hin | apply Z.eqb_refl]. }
  split; [exact D|]. pose proof (declared_range _ D). lia.
Qed.
