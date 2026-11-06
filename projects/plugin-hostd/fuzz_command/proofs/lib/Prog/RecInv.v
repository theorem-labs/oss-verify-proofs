From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
Import ListNotations.
Open Scope Z_scope.

Definition REC_SIZE : Z := 960.
Definition SC_SIZE : Z := 56.
Definition CALL_SIZE : Z := 56.
Definition OFF_REFUSE : Z := 0.
Definition OFF_CODE : Z := 4.
Definition OFF_NCALLS : Z := 8.
Definition OFF_CALLS : Z := 16.
Definition OFF_ANSWER : Z := 912.
Definition OFF_NREPLIES : Z := 920.
Definition OFF_REPLY : Z := 928.
Definition OFF_REPLY_SIZE : Z := 936.
Definition OFF_STATE : Z := 944.
Definition OFF_HOST : Z := 952.
Definition CALL_OFF_FN : Z := 0.
Definition CALL_OFF_NARGS : Z := 4.
Definition CALL_OFF_ARGS : Z := 8.

Definition iv_apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.

Record rlay := RLay {
  l_calls : list (list (Z * Z));
  l_spill : list (Z * Z);
  l_answer : option (Z * Z);
  l_reply : option (Z * Z) }.

Definition oblk (q : option (Z * Z)) : list (Z * Z) := match q with Some pn => [pn] | None => [] end.

Definition lay_blocks (Q : rlay) : list (Z * Z) :=
  concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q).

Section Rep.
Variable segs : list Segment.

Definition call_at (bl : list (Z * Z)) (mem : word -> option byte) (a : Z) (c : rcall) (P : list (Z * Z)) : Prop :=
  0 <= fst c < REC_FN_COUNT /\ (length (snd c) <= 6)%nat /\ length P = length (snd c) /\
  bytes_at segs mem (a + CALL_OFF_FN) (le4 (Z_to_bv 64 (fst c))) /\
  bytes_at segs mem (a + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length (snd c))))) /\
  NoDup (map fst P) /\
  forall k s pn, nth_error (snd c) k = Some s -> nth_error P k = Some pn ->
    bytes_at segs mem (a + CALL_OFF_ARGS + 8 * Z.of_nat k) (le8 (Z_to_bv 64 (fst pn))) /\
    fst pn <> 0 /\ In pn bl /\ Z.of_nat (length s) + 1 <= snd pn <= LMAX + 2 /\
    bytes_at segs mem (fst pn) (s ++ [Z_to_bv 8 0]) /\ no0 s.

Definition records (bl : list (Z * Z)) (mem : word -> option byte) (a fn : Z) (A : list (list byte)) : Prop :=
  exists P, call_at bl mem a (fn, A) P.

Definition answer_at (bl : list (Z * Z)) (mem : word -> option byte) (gr : Z)
    (t : option (list byte)) (q : option (Z * Z)) : Prop :=
  match t, q with
  | None, None => bytes_at segs mem (gr + OFF_ANSWER) (le8 (Z_to_bv 64 0))
  | Some x, Some pn =>
      bytes_at segs mem (gr + OFF_ANSWER) (le8 (Z_to_bv 64 (fst pn))) /\
      fst pn <> 0 /\ In pn bl /\ Z.of_nat (length x) + 1 <= snd pn <= LMAX + 2 /\
      bytes_at segs mem (fst pn) (x ++ [Z_to_bv 8 0]) /\ no0 x /\ Z.of_nat (length x) <= LMAX
  | _, _ => False
  end.

Definition reply_at (bl : list (Z * Z)) (mem : word -> option byte) (gr : Z)
    (y : option (list byte)) (q : option (Z * Z)) : Prop :=
  match y, q with
  | None, None =>
      bytes_at segs mem (gr + OFF_REPLY) (le8 (Z_to_bv 64 0)) /\
      bytes_at segs mem (gr + OFF_REPLY_SIZE) (le8 (Z_to_bv 64 0))
  | Some x, Some pn =>
      bytes_at segs mem (gr + OFF_REPLY) (le8 (Z_to_bv 64 (fst pn))) /\
      bytes_at segs mem (gr + OFF_REPLY_SIZE) (le8 (Z_to_bv 64 (Z.of_nat (length x)))) /\
      fst pn <> 0 /\ x <> [] /\ In pn bl /\ Z.of_nat (length x) <= snd pn <= LMAX + 2 /\
      bytes_at segs mem (fst pn) x /\ Z.of_nat (length x) <= LMAX + 2
  | _, _ => False
  end.

Definition g1_storage (mem : word -> option byte) (gr sc : Z) : Prop :=
  gr mod 8 = 0 /\ sc mod 8 = 0 /\ iv_apart gr REC_SIZE sc SC_SIZE /\
  wr_at segs mem gr REC_SIZE /\ wr_at segs mem sc SC_SIZE.

Definition g1_calls (bl : list (Z * Z)) (mem : word -> option byte) (gr sc : Z) (R : rstate) (Q : rlay) : Prop :=
  (length (r_calls R) <= 16)%nat /\ length (l_calls Q) = length (r_calls R) /\
  bytes_at segs mem (gr + OFF_NCALLS) (le4 (Z_to_bv 64 (Z.of_nat (length (r_calls R))))) /\
  (forall i c P, nth_error (r_calls R) i = Some c -> nth_error (l_calls Q) i = Some P ->
     call_at bl mem (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\
     Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)) /\
  call_at bl mem sc (r_spill R) (l_spill Q) /\
  Forall (fun s => Z.of_nat (length s) <= LMAX) (snd (r_spill R)).

Definition g1_scalars (mem : word -> option byte) (gr : Z) (R : rstate) : Prop :=
  bytes_at segs mem (gr + OFF_REFUSE) (le4 (Z_to_bv 64 (r_refuse R))) /\
  bytes_at segs mem (gr + OFF_CODE) (le4 (Z_to_bv 64 (r_code R))) /\
  bytes_at segs mem (gr + OFF_NREPLIES) (le4 (Z_to_bv 64 (r_nreplies R))) /\
  bytes_at segs mem (gr + OFF_STATE) (le8 (Z_to_bv 64 (r_state R))) /\
  bytes_at segs mem (gr + OFF_HOST) (le8 (Z_to_bv 64 (r_host R))) /\
  -2^31 <= r_refuse R < 2^31 /\ -2^31 <= r_code R < 2^31 /\ 0 <= r_nreplies R < 2^31 /\
  0 <= r_state R < 2^64 /\ 0 <= r_host R < 2^64.

Definition g1_own (gr sc : Z) (Q : rlay) : Prop :=
  NoDup (map fst (lay_blocks Q)) /\
  forall pn, In pn (lay_blocks Q) -> iv_apart (fst pn) (snd pn) gr REC_SIZE /\ iv_apart (fst pn) (snd pn) sc SC_SIZE.

Definition rep_at (bl : list (Z * Z)) (mem : word -> option byte) (gr sc : Z) (R : rstate) (Q : rlay) : Prop :=
  g1_storage mem gr sc /\
  g1_calls bl mem gr sc R Q /\
  answer_at bl mem gr (r_answer R) (l_answer Q) /\
  reply_at bl mem gr (r_reply R) (l_reply Q) /\
  g1_scalars mem gr R /\
  g1_own gr sc Q.

Definition rec_rep (gr sc : Z) (L : layout) (A : astate) (mem : word -> option byte) (R : rstate)
    (O : list (Z * Z)) : Prop :=
  exists Q, rep_at (blocks L A) mem gr sc R Q /\ (forall pn, In pn O <-> In pn (lay_blocks Q)).

Definition rec_G1 (gr sc : Z) (L : layout) (A : astate) (mem : word -> option byte) : Prop :=
  exists R O, rec_rep gr sc L A mem R O.

Lemma bytes_at_keep : forall m m' a bs,
  bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  bytes_at segs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H2) K. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H2 i Hi). exact (K (Z.of_nat i) ltac:(lia)).
Qed.

Lemma bytes_at_keep_in : forall m m' lo hi a bs,
  bytes_at segs m a bs -> lo <= a -> a + Z.of_nat (length bs) <= hi ->
  (forall x, lo <= x < hi -> mbyte segs m' x = mbyte segs m x) ->
  bytes_at segs m' a bs.
Proof. intros m m' lo hi a bs H Hlo Hhi K. apply (bytes_at_keep m); [exact H|]. intros i Hi. apply K. lia. Qed.

Lemma wr_at_keep : forall m m' a n,
  wr_at segs m a n ->
  (forall i, 0 <= i < n -> writable_at segs m (a + i) -> writable_at segs m' (a + i)) ->
  wr_at segs m' a n.
Proof.
  intros m m' a n (H0 & H1 & H2) K. split; [exact H0|]. split; [exact H1|].
  intros i Hi. exact (K i Hi (H2 i Hi)).
Qed.

Lemma call_at_keep : forall bl bl' m m' a c P,
  call_at bl m a c P ->
  (forall x, a <= x < a + CALL_SIZE -> mbyte segs m' x = mbyte segs m x) ->
  (forall pn, In pn P -> In pn bl' /\
     forall i, 0 <= i < snd pn -> mbyte segs m' (fst pn + i) = mbyte segs m (fst pn + i)) ->
  call_at bl' m' a c P.
Proof.
  intros bl bl' m m' a c P (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk) K KP.
  unfold call_at. unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  split; [exact Hfn|]. split; [exact Hn|]. split; [exact Hl|].
  split; [apply (bytes_at_keep_in m m' a (a + 56)); [exact Hb0 | lia | rewrite length_le4; lia | exact K]|].
  split; [apply (bytes_at_keep_in m m' a (a + 56)); [exact Hb1 | lia | rewrite length_le4; lia | exact K]|].
  split; [exact Hnd|].
  intros k s pn Es Ep. destruct (Hk k s pn Es Ep) as (Hs & Hp0 & Hin & Hsz & Hstr & Hno).
  assert (Hkl : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  destruct (KP pn (nth_error_In P k Ep)) as [Hin' Kp].
  split; [apply (bytes_at_keep_in m m' a (a + 56)); [exact Hs | lia | rewrite length_le8; lia | exact K]|].
  split; [exact Hp0|]. split; [exact Hin'|]. split; [exact Hsz|]. split; [|exact Hno].
  apply (bytes_at_keep m); [exact Hstr|]. intros i Hi. apply Kp. rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.

Lemma rec_rep_frame : forall gr sc L A mem R O L' A' mem',
  rec_rep gr sc L A mem R O ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a -> writable_at segs mem' a)) ->
  (forall p n i, In (p, n) O -> 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) ->
  (forall pn, In pn O -> In pn (blocks L' A')) ->
  rec_rep gr sc L' A' mem' R O.
Proof.
  intros gr sc L A mem R O L' A' mem' (Q & HR & HO) KG KB KL.
  exists Q. split; [|exact HO].
  unfold rep_at, g1_storage, g1_calls, g1_scalars, g1_own, answer_at, reply_at in *.
  destruct HR as (HS & HC & HA & HP & HX & HW).
  assert (KG1 : forall x, gr <= x < gr + REC_SIZE -> mbyte segs mem' x = mbyte segs mem x)
    by (intros x Hx; apply KG; left; exact Hx).
  assert (KS1 : forall x, sc <= x < sc + SC_SIZE -> mbyte segs mem' x = mbyte segs mem x)
    by (intros x Hx; apply KG; right; exact Hx).
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (blocks L' A') /\
     forall i, 0 <= i < snd pn -> mbyte segs mem' (fst pn + i) = mbyte segs mem (fst pn + i)).
  { intros [p n] Hpn. apply HO in Hpn. split; [apply KL; exact Hpn|]. intros i Hi. exact (KB p n i Hpn Hi). }
  unfold REC_SIZE, SC_SIZE, OFF_REFUSE, OFF_CODE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_NREPLIES, OFF_REPLY,
    OFF_REPLY_SIZE, OFF_STATE, OFF_HOST, CALL_SIZE in *.
  split; [| split; [| split; [| split]]].
  - destruct HS as (H1 & H2 & H3 & H4 & H5). refine (conj H1 (conj H2 (conj H3 (conj _ _)))).
    + apply (wr_at_keep mem); [exact H4|]. intros i Hi.
      assert (Hx : gr <= gr + i < gr + 960) by lia. exact (proj2 (KG (gr + i) (or_introl Hx))).
    + apply (wr_at_keep mem); [exact H5|]. intros i Hi.
      assert (Hx : sc <= sc + i < sc + 56) by lia. exact (proj2 (KG (sc + i) (or_intror Hx))).
  - destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (bytes_at_keep_in mem mem' gr (gr + 960)); [exact C3 | lia | rewrite length_le4; lia | exact KG1].
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hil : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (call_at_keep (blocks L A) (blocks L' A') mem mem'); [exact Hc | |].
      * intros x Hx. apply KG1. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + apply (call_at_keep (blocks L A) (blocks L' A') mem mem'); [exact C5 | |].
      * intros x Hx. apply KS1. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - revert HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [[p n]|] eqn:EA; intros HA; try contradiction.
    + destruct HA as (N1 & N2 & N3 & N4 & N5 & N6 & N7). cbn [fst snd] in *.
      assert (Hq : In (p, n) (lay_blocks Q)).
      { unfold lay_blocks. rewrite EA. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
        left. reflexivity. }
      destruct (KQ (p, n) Hq) as [Kin Kp]. cbn [fst snd] in Kp.
      split; [apply (bytes_at_keep_in mem mem' gr (gr + 960)); [exact N1 | lia | rewrite length_le8; lia | exact KG1]|].
      split; [exact N2|]. split; [exact Kin|]. split; [exact N4|].
      split; [|split; [exact N6 | exact N7]].
      apply (bytes_at_keep mem); [exact N5|]. intros i Hi. apply Kp. rewrite length_app in Hi. cbn [length] in Hi. lia.
    + apply (bytes_at_keep_in mem mem' gr (gr + 960)); [exact HA | lia | rewrite length_le8; lia | exact KG1].
  - revert HP. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [[p n]|] eqn:EP; intros HP; try contradiction.
    + destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). cbn [fst snd] in *.
      assert (Hq : In (p, n) (lay_blocks Q)).
      { unfold lay_blocks. rewrite EP. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
        left. reflexivity. }
      destruct (KQ (p, n) Hq) as [Kin Kp]. cbn [fst snd] in Kp.
      split; [apply (bytes_at_keep_in mem mem' gr (gr + 960)); [exact P1 | lia | rewrite length_le8; lia | exact KG1]|].
      split; [apply (bytes_at_keep_in mem mem' gr (gr + 960)); [exact P2 | lia | rewrite length_le8; lia | exact KG1]|].
      split; [exact P3|]. split; [exact P4|]. split; [exact Kin|]. split; [exact P6|].
      split; [|exact P8].
      apply (bytes_at_keep mem); [exact P7|]. intros i Hi. apply Kp. lia.
    + destruct HP as [P1 P2].
      split; [apply (bytes_at_keep_in mem mem' gr (gr + 960)); [exact P1 | lia | rewrite length_le8; lia | exact KG1]|].
      apply (bytes_at_keep_in mem mem' gr (gr + 960)); [exact P2 | lia | rewrite length_le8; lia | exact KG1].
  - split; [|exact HW].
    destruct HX as (X1 & X2 & X3 & X4 & X5 & X6).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
    + apply (bytes_at_keep_in mem mem' gr (gr + 960)); [exact X1 | lia | rewrite length_le4; lia | exact KG1].
    + apply (bytes_at_keep_in mem mem' gr (gr + 960)); [exact X2 | lia | rewrite length_le4; lia | exact KG1].
    + apply (bytes_at_keep_in mem mem' gr (gr + 960)); [exact X3 | lia | rewrite length_le4; lia | exact KG1].
    + apply (bytes_at_keep_in mem mem' gr (gr + 960)); [exact X4 | lia | rewrite length_le8; lia | exact KG1].
    + apply (bytes_at_keep_in mem mem' gr (gr + 960)); [exact X5 | lia | rewrite length_le8; lia | exact KG1].
Qed.

Lemma rec_rep_records : forall gr sc L A mem R O i c,
  rec_rep gr sc L A mem R O -> nth_error (r_calls R) i = Some c ->
  records (blocks L A) mem (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i) (fst c) (snd c).
Proof.
  intros gr sc L A mem R O i [fn As] (Q & (HS & HC & _) & _) Ec.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  destruct (nth_error (l_calls Q) i) as [P|] eqn:EP.
  - exists P. exact (proj1 (C4 i (fn, As) P Ec EP)).
  - exfalso. apply nth_error_None in EP.
    assert (Hil : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate). lia.
Qed.

Lemma rec_rep_spill_records : forall gr sc L A mem R O,
  rec_rep gr sc L A mem R O -> records (blocks L A) mem sc (fst (r_spill R)) (snd (r_spill R)).
Proof.
  intros gr sc L A mem R O (Q & (HS & HC & _) & _). destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  exists (l_spill Q). revert C5. destruct (r_spill R) as [fn As]. intros C5. exact C5.
Qed.

Lemma rec_rep_G1 : forall gr sc L A mem R O, rec_rep gr sc L A mem R O -> rec_G1 gr sc L A mem.
Proof. intros gr sc L A mem R O H. exists R, O. exact H. Qed.

End Rep.
