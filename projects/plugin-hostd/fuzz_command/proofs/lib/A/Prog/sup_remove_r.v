(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the recorder-side steps of plugin-hostd/fuzz_command's sup_connect walk.

   sup_connect (recorder.c:336-345, record() and arg_s inlined :205-227) changes the recorder in two kinds of step.
   record() reads g_rec.ncalls = n; for n < 16 it stores ncalls := n + 1 and takes the slot
   c = g_rec + OFF_CALLS + CALL_SIZE * n, else (after rec_calls_free(&record.spill, 1)) the slot c = record.spill;
   then it stores c->fn := fn and c->nargs := 0. Each argument then stores c->nargs := m + 1 and c->args[m] := p,
   with p a fresh block that holds the argument string. The model is lib/Prog/RecModel.v:38-39 (rec_record).

   This file states those steps over lib/A/Prog/CmdRep.v's arep_at / rec_repA, for any reader: the record step for
   each arm (scn_record_lt, scn_record_full) and the append step (scn_append_call, scn_append_spill, and scn_append,
   which takes either slot). The proofs are the plain proof's lib/Prog/RecStep.v (rec_rep_record_lt :63-178,
   rep_at_record_full :395-440, call_at_arg :442-485, rep_at_arg_lt :487-580, rep_at_arg_full :582-648,
   rec_rep_arg :650-699) over the reader, without the writability conjuncts that arep_at drops.

   Each step asks that the reader keep every byte it does not write, but only the bytes of g_rec, of record.spill
   and of the recorder's own live blocks: that is what a callee's journal gives, and an inline store gives more. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_connect_s2.v, with its numbers changed; 388 of its 456 lines of code are new or changed and 572 lines of the source are left out. *)
(* The recorder-representation steps of sup_remove's walk (lib/A/Prog/sup_remove_c.v): the call that record()
   adds is recorded either in the next table slot (index length (r_calls R) < 16) or in record.spill, and the
   reader-level facts about arep_at (lib/A/Prog/CmdRep.v) that the walk's assembly reads off the recorder state:
   the answer word, the ncalls word, the live and distinct recorder blocks, the spill's arguments dropped from the
   block set, and rec_calls_free's premises for the spill slot. These are pure lemmas over a reader; they mirror
   the plain proof's lib/Prog/RecStep.v (rec_rep_record_lt, rep_at_record_full, lay_drop_spill). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

(* ---- transport of the reader forms across a reader that keeps the bytes they read ---- *)

Lemma srr_aval_keep_in : forall rd rd' a n v lo hi, aval_mem rd a n v -> lo <= a -> a + Z.of_nat n <= hi ->
  (forall x, lo <= x < hi -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v lo hi H H1 H2 K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma srr_aval_addr : forall rd a b n v, a = b -> aval_mem rd a n v -> aval_mem rd b n v.
Proof. intros rd a b n v -> H. exact H. Qed.

Lemma srr_abytes_keep : forall rd rd' a l, abytes_atR rd a l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma srr_astr_keep : forall rd rd' p s, astr_atR rd p s ->
  (forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H N] K. split; [|exact N]. apply (srr_abytes_keep rd); [exact H|].
  intros i Hi. apply K. rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.

Lemma srr_acall_keep : forall bl bl' rd rd' a c P,
  acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) KA KP.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [apply (srr_aval_keep_in rd rd' _ _ _ a (a + CALL_SIZE));
          [exact H4 | unfold CALL_OFF_FN; lia | unfold CALL_OFF_FN, CALL_SIZE; lia | exact KA]|].
  split; [apply (srr_aval_keep_in rd rd' _ _ _ a (a + CALL_SIZE));
          [exact H5 | unfold CALL_OFF_NARGS; lia | unfold CALL_OFF_NARGS, CALL_SIZE; lia | exact KA]|].
  split; [exact H6|].
  intros k s pn Es Ep.
  destruct (H7 k s pn Es Ep) as (G1 & G2 & G3 & G4 & G5).
  assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  assert (Hin : In pn P) by (eapply nth_error_In; exact Ep).
  destruct (KP pn Hin) as [B1 B2].
  split; [apply (srr_aval_keep_in rd rd' _ _ _ a (a + CALL_SIZE));
          [exact G1 | unfold CALL_OFF_ARGS; lia | unfold CALL_OFF_ARGS, CALL_SIZE; lia | exact KA]|].
  split; [exact G2|]. split; [exact B1|]. split; [exact G4|].
  apply (srr_astr_keep rd); [exact G5|]. intros i Hi. apply B2. lia.
Qed.

Lemma srr_ans_keep : forall bl bl' rd rd' gr t qa,
  aanswer_at bl rd gr t qa ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk qa) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  aanswer_at bl' rd' gr t qa.
Proof.
  intros bl bl' rd rd' gr t qa H K KB.
  destruct t as [x|]; destruct qa as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
  - destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KB pn ltac:(cbn [oblk In]; left; reflexivity)) as [B1 B2].
    refine (conj _ (conj N2 (conj B1 (conj N4 (conj _ N6))))).
    + apply (srr_aval_keep_in rd rd' _ _ _ (gr + OFF_ANSWER) (gr + OFF_ANSWER + 8)); [exact N1 | lia | lia | exact K].
    + apply (srr_astr_keep rd); [exact N5|]. intros i Hi. apply B2. lia.
  - apply (srr_aval_keep_in rd rd' _ _ _ (gr + OFF_ANSWER) (gr + OFF_ANSWER + 8)); [exact H | lia | lia | exact K].
Qed.

Lemma srr_rep_keep : forall bl bl' rd rd' gr y qr,
  areply_at bl rd gr y qr ->
  (forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY + 16 -> rd' x = rd x) ->
  (forall pn, In pn (oblk qr) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  areply_at bl' rd' gr y qr.
Proof.
  intros bl bl' rd rd' gr y qr H K KB.
  destruct y as [x|]; destruct qr as [pn|]; cbn [areply_at] in H |- *; try contradiction.
  - destruct H as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    destruct (KB pn ltac:(cbn [oblk In]; left; reflexivity)) as [B1 B2].
    refine (conj _ (conj _ (conj P3 (conj P4 (conj B1 (conj P6 (conj _ P8))))))).
    + apply (srr_aval_keep_in rd rd' _ _ _ (gr + OFF_REPLY) (gr + OFF_REPLY + 16));
        [exact P1 | lia | lia | exact K].
    + apply (srr_aval_keep_in rd rd' _ _ _ (gr + OFF_REPLY) (gr + OFF_REPLY + 16));
        [exact P2 | unfold OFF_REPLY, OFF_REPLY_SIZE; lia | unfold OFF_REPLY, OFF_REPLY_SIZE; lia | exact K].
    + apply (srr_abytes_keep rd); [exact P7|]. intros i Hi. apply B2. lia.
  - destruct H as [P1 P2]. split.
    + apply (srr_aval_keep_in rd rd' _ _ _ (gr + OFF_REPLY) (gr + OFF_REPLY + 16));
        [exact P1 | lia | lia | exact K].
    + apply (srr_aval_keep_in rd rd' _ _ _ (gr + OFF_REPLY) (gr + OFF_REPLY + 16));
        [exact P2 | unfold OFF_REPLY, OFF_REPLY_SIZE; lia | unfold OFF_REPLY, OFF_REPLY_SIZE; lia | exact K].
Qed.

Lemma srr_scalars_keep : forall rd rd' gr R, ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R H K. unfold ag1_scalars in *. destruct H as (X1 & X2 & X3 & X4 & X5 & X6).
  unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  - apply (srr_aval_keep_in rd rd' _ _ _ gr (gr + 4)); [exact X1 | lia | lia | intros x Hx; apply K; lia].
  - apply (srr_aval_keep_in rd rd' _ _ _ (gr + 4) (gr + 8)); [exact X2 | lia | lia | intros x Hx; apply K; lia].
  - apply (srr_aval_keep_in rd rd' _ _ _ (gr + 920) (gr + 924)); [exact X3 | lia | lia | intros x Hx; apply K; lia].
  - apply (srr_aval_keep_in rd rd' _ _ _ (gr + 944) (gr + 952)); [exact X4 | lia | lia | intros x Hx; apply K; lia].
  - apply (srr_aval_keep_in rd rd' _ _ _ (gr + 952) (gr + 960)); [exact X5 | lia | lia | intros x Hx; apply K; lia].
Qed.

(* ---- list facts ---- *)

Lemma srr_lnodup_app_disj : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x H H1 H2; [destruct H1|].
  cbn [app] in H. apply List.NoDup_cons_iff in H as [Hy Hl].
  destruct H1 as [E|H1].
  - subst. apply Hy. apply in_or_app. right. exact H2.
  - exact (IH l2 x Hl H1 H2).
Qed.

Lemma srr_nodup_fst_disj : forall (l1 l2 : list (Z * Z)) pn qn, NoDup (map fst (l1 ++ l2)) ->
  In pn l1 -> In qn l2 -> fst pn <> fst qn.
Proof.
  intros l1 l2 pn qn H H1 H2 E. apply NoDup_ListNoDup in H. rewrite map_app in H.
  apply (srr_lnodup_app_disj (map fst l1) (map fst l2) (fst pn) H); [apply in_map; exact H1|].
  rewrite E. apply in_map. exact H2.
Qed.

Lemma srr_lnodup_ins : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> ~ In x (l1 ++ l2) ->
  List.NoDup (l1 ++ x :: l2).
Proof.
  induction l1 as [|y l1 IH]; intros l2 x H N; cbn [app] in *.
  - constructor; assumption.
  - apply List.NoDup_cons_iff in H as [Hy Hl]. constructor.
    + intros Hin. apply in_app_or in Hin as [Hin|[E|Hin]].
      * apply Hy. apply in_or_app. left. exact Hin.
      * subst. apply N. left. reflexivity.
      * apply Hy. apply in_or_app. right. exact Hin.
    + apply IH; [exact Hl|]. intros Hin. apply N. right. exact Hin.
Qed.

Lemma srr_in_mid : forall (X W : list (Z * Z)) a pn, In pn (X ++ a :: W) -> pn = a \/ In pn (X ++ W).
Proof.
  intros X W a pn H. apply in_app_or in H as [H|[H|H]].
  - right. apply in_or_app. left. exact H.
  - left. symmetry. exact H.
  - right. apply in_or_app. right. exact H.
Qed.

Lemma srr_add8_0 : forall z, z + 8 * Z.of_nat 0 = z.
Proof. intros z. lia. Qed.

Lemma srr_rec_record_lt : forall R fn A, (length (r_calls R) < 16)%nat ->
  rec_record R fn A = set_calls R (r_calls R ++ [(fn, A)]).
Proof. intros R fn A H. unfold rec_record. apply Nat.ltb_lt in H. rewrite H. reflexivity. Qed.

Lemma srr_lay_slot : forall Q pk,
  lay_blocks (RLay (l_calls Q ++ [[pk]]) (l_spill Q) (l_answer Q) (l_reply Q)) =
  concat (l_calls Q) ++ pk :: (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)).
Proof.
  intros Q pk. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma srr_lay_spill : forall Q pk, l_spill Q = [] ->
  lay_blocks (RLay (l_calls Q) [pk] (l_answer Q) (l_reply Q)) =
  concat (l_calls Q) ++ pk :: (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)).
Proof. intros Q pk E. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite E. reflexivity. Qed.

Lemma srr_acall_live : forall bl rd a c P pn, acall_at bl rd a c P -> In pn P ->
  In pn bl /\ 1 <= snd pn /\ fst pn <> 0.
Proof.
  intros bl rd a c P pn (_ & _ & Hl & _ & _ & _ & Hk) Hin.
  destruct (In_nth_error P pn Hin) as [k Ek].
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (Hk k s pn Es Ek) as (_ & G2 & G3 & G4 & _). split; [exact G3|]. split; [lia | exact G2].
Qed.

(* the recorder's own block set gains one fresh block pk *)
Lemma srr_own_ins : forall gr sc Q Q' X W pk,
  lay_blocks Q = X ++ W -> lay_blocks Q' = X ++ pk :: W ->
  ag1_own gr sc Q ->
  (forall qn, In qn (lay_blocks Q) -> 1 <= snd qn) -> 1 <= snd pk ->
  (forall qn, In qn (lay_blocks Q) -> iv_apart (fst pk) (snd pk) (fst qn) (snd qn)) ->
  iv_apart (fst pk) (snd pk) gr REC_SIZE -> iv_apart (fst pk) (snd pk) sc SC_SIZE ->
  ag1_own gr sc Q'.
Proof.
  intros gr sc Q Q' X W pk E E' (W1 & W2) L1 Lk AP AG AS.
  unfold ag1_own. rewrite E'. rewrite E in W1, W2, L1, AP. split.
  - apply NoDup_ListNoDup in W1. apply NoDup_ListNoDup. rewrite map_app in W1 |- *. cbn [map].
    apply srr_lnodup_ins; [exact W1|]. rewrite <- map_app. intros Hin.
    apply in_map_iff in Hin as (qn & Eq & Hq).
    specialize (AP qn Hq). specialize (L1 qn Hq). unfold iv_apart in AP. lia.
  - intros pn Hpn. apply srr_in_mid in Hpn as [->|Hpn]; [split; [exact AG | exact AS] | exact (W2 pn Hpn)].
Qed.

(* ---- the walk's lemmas ---- *)

(* the recorder's blocks are live and non-empty, and their starts differ *)
Lemma sr_lay_live : forall bl rd gr sc R Q, arep_at bl rd gr sc R Q ->
  NoDup (map fst (lay_blocks Q)) /\ forall pn, In pn (lay_blocks Q) -> In pn bl /\ 1 <= snd pn /\ fst pn <> 0.
Proof.
  intros bl rd gr sc R Q (S1 & S2 & S3 & HC & HA & HY & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6). destruct HW as [W1 W2].
  split; [exact W1|]. intros pn Hpn. unfold lay_blocks in Hpn.
  apply in_app_or in Hpn as [Hpn|Hpn].
  - apply in_concat in Hpn as (P & HP0 & HPn).
    destruct (In_nth_error _ _ HP0) as [i EP].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite EP; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    exact (srr_acall_live _ _ _ _ _ _ (proj1 (C4 i c P Ec EP)) HPn).
  - apply in_app_or in Hpn as [Hpn|Hpn]; [exact (srr_acall_live _ _ _ _ _ _ C5 Hpn)|].
    apply in_app_or in Hpn as [Hpn|Hpn].
    + revert HA Hpn. destruct (r_answer R) as [x|]; destruct (l_answer Q) as [qa|];
        cbn [aanswer_at oblk In]; intros HA Hpn; try contradiction.
      destruct Hpn as [E|[]]. subst qa. destruct HA as (_ & N2 & N3 & N4 & _).
      split; [exact N3|]. split; [lia | exact N2].
    + revert HY Hpn. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [qr|];
        cbn [areply_at oblk In]; intros HY Hpn; try contradiction.
      destruct Hpn as [E|[]]. subst qr. destruct HY as (_ & _ & P3 & P4 & P5 & P6 & _).
      split; [exact P5|]. split; [|exact P3].
      destruct x as [|b x]; [exfalso; apply P4; reflexivity | cbn [length] in P6; lia].
Qed.

(* the new call recorded in table slot n = length (r_calls R) *)
Lemma sr_rep_slot : forall (bl bl' : list (Z * Z)) (rd rd' : reader) (R : rstate) (Q : rlay) (fn p : Z) (s : list byte),
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (length (r_calls R) < 16)%nat ->
  0 <= fn < REC_FN_COUNT ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
  aval_mem rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_NARGS) 4 1 ->
  aval_mem rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_ARGS) 8 p ->
  astr_atR rd' p s -> Z.of_nat (length s) <= LMAX ->
  p <> 0 -> In (p, Z.of_nat (length s) + 1) bl' ->
  iv_apart p (Z.of_nat (length s) + 1) A_G_REC REC_SIZE -> iv_apart p (Z.of_nat (length s) + 1) A_REC_SPILL SC_SIZE ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl' /\ iv_apart p (Z.of_nat (length s) + 1) (fst pn) (snd pn)) ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
     ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
     ~ (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) <= a <
        A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + 16) -> rd' a = rd a) ->
  (forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R fn [s])
    (RLay (l_calls Q ++ [[(p, Z.of_nat (length s) + 1)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
  intros bl bl' rd rd' R Q fn p s HR Hn Hfn BN BF BA BP Hs HL Hp0 Hbl AG AS AQ KG KQ.
  destruct (sr_lay_live bl rd A_G_REC A_REC_SPILL R Q HR) as [_ LV].
  destruct HR as (S1 & S2 & S3 & HC & HA & HY & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  rewrite (srr_rec_record_lt R fn [s] Hn).
  assert (KB : forall pn, In pn (lay_blocks Q) -> In pn bl' /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
  { intros pn Hpn. split; [exact (proj1 (AQ pn Hpn)) | intros i Hi; exact (KQ pn i Hpn Hi)]. }
  assert (KR : forall x, A_G_REC <= x < A_G_REC + 960 -> ~ (A_G_REC + 8 <= x < A_G_REC + 12) ->
            ~ (A_G_REC + 16 + 56 * Z.of_nat (length (r_calls R)) <= x <
               A_G_REC + 16 + 56 * Z.of_nat (length (r_calls R)) + 16) -> rd' x = rd x).
  { intros x H1 H2 H3. apply KG; [left; unfold REC_SIZE; exact H1 | unfold OFF_NCALLS; lia |
      unfold OFF_CALLS, CALL_SIZE; lia]. }
  assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + 56 -> rd' x = rd x).
  { intros x Hx. apply KG; unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *;
      lia. }
  unfold arep_at, ag1_calls.
  cbn [set_calls r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
  split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  split; [|split; [|split; [|split]]].
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ C6))))).
    + rewrite length_app. cbn [length]. lia.
    + rewrite !length_app, C2. reflexivity.
    + rewrite length_app, Nat2Z.inj_add. exact BN.
    + intros i c P Ec EP.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      * rewrite nth_error_app1 in Ec by exact Hi. rewrite nth_error_app1 in EP by (rewrite C2; exact Hi).
        destruct (C4 i c P Ec EP) as [Hc HLc]. split; [|exact HLc].
        apply (srr_acall_keep bl bl' rd rd'); [exact Hc | |].
        -- intros x Hx. unfold CALL_SIZE, OFF_CALLS in Hx. apply KR; lia.
        -- intros pn Hpn. apply KB. unfold lay_blocks. apply in_or_app. left. apply in_concat.
           exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
      * destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
        -- rewrite nth_error_app2 in Ec by lia. rewrite Nat.sub_diag in Ec. cbn in Ec. injection Ec as <-.
           rewrite nth_error_app2 in EP by lia. rewrite C2, Nat.sub_diag in EP. cbn in EP. injection EP as <-.
           split; [|constructor; [exact HL | constructor]].
           unfold acall_at. cbn [fst snd length].
           split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
           split; [exact BF|]. split; [exact BA|].
           split; [apply NoDup_ListNoDup; cbn [map]; constructor; [intros [] | constructor]|].
           intros k s0 pn Es Ep. destruct k as [|k]; [|cbn in Es; destruct k; discriminate].
           cbn in Es, Ep. injection Es as <-. injection Ep as <-. cbn [fst snd].
           split; [rewrite srr_add8_0; exact BP|].
           split; [exact Hp0|]. split; [exact Hbl|]. split; [lia|]. exact Hs.
        -- exfalso. assert (N : nth_error (r_calls R ++ [(fn, [s])]) i = None)
             by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
           rewrite N in Ec. discriminate.
    + apply (srr_acall_keep bl bl' rd rd'); [exact C5 | |].
      * intros x Hx. unfold CALL_SIZE in Hx. apply KS. lia.
      * intros pn Hpn. apply KB. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - apply (srr_ans_keep bl bl' rd rd' _ _ _ HA).
    + intros x Hx. unfold OFF_ANSWER in Hx. apply KR; lia.
    + intros pn Hpn. apply KB. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left. exact Hpn.
  - apply (srr_rep_keep bl bl' rd rd' _ _ _ HY).
    + intros x Hx. unfold OFF_REPLY in Hx. apply KR; lia.
    + intros pn Hpn. apply KB. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact Hpn.
  - exact (srr_scalars_keep rd rd' A_G_REC R HX ltac:(intros x Hx; apply KR; lia)).
  - exact (srr_own_ins A_G_REC A_REC_SPILL Q _ (concat (l_calls Q))
             (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)) (p, Z.of_nat (length s) + 1)
             eq_refl (srr_lay_slot Q _) HW (fun qn Hq => proj1 (proj2 (LV qn Hq)))
             ltac:(cbn [snd]; lia) (fun qn Hq => proj2 (AQ qn Hq)) AG AS).
Qed.

(* the new call recorded in record.spill, whose arguments were freed (r_spill R holds no argument) *)
Lemma sr_rep_spill : forall (bl bl' : list (Z * Z)) (rd rd' : reader) (R : rstate) (Q : rlay) (fn p : Z) (s : list byte),
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  snd (r_spill R) = [] ->
  0 <= fn < REC_FN_COUNT ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 1 ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_ARGS) 8 p ->
  astr_atR rd' p s -> Z.of_nat (length s) <= LMAX ->
  p <> 0 -> In (p, Z.of_nat (length s) + 1) bl' ->
  iv_apart p (Z.of_nat (length s) + 1) A_G_REC REC_SIZE -> iv_apart p (Z.of_nat (length s) + 1) A_REC_SPILL SC_SIZE ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl' /\ iv_apart p (Z.of_nat (length s) + 1) (fst pn) (snd pn)) ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
     ~ (A_REC_SPILL <= a < A_REC_SPILL + 16) -> rd' a = rd a) ->
  (forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  arep_at bl' rd' A_G_REC A_REC_SPILL (set_spill R (fn, [s]))
    (RLay (l_calls Q) [(p, Z.of_nat (length s) + 1)] (l_answer Q) (l_reply Q)).
Proof.
  intros bl bl' rd rd' R Q fn p s HR Hsp Hfn BF BA BP Hs HL Hp0 Hbl AG AS AQ KG KQ.
  destruct (sr_lay_live bl rd A_G_REC A_REC_SPILL R Q HR) as [_ LV].
  destruct HR as (S1 & S2 & S3 & HC & HA & HY & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  assert (ES : l_spill Q = []).
  { destruct C5 as (_ & _ & E & _). rewrite Hsp in E. destruct (l_spill Q); [reflexivity | discriminate]. }
  assert (KB : forall pn, In pn (lay_blocks Q) -> In pn bl' /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
  { intros pn Hpn. split; [exact (proj1 (AQ pn Hpn)) | intros i Hi; exact (KQ pn i Hpn Hi)]. }
  assert (KR : forall x, A_G_REC <= x < A_G_REC + 960 -> rd' x = rd x).
  { intros x Hx. apply KG; unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in *; lia. }
  unfold arep_at, ag1_calls.
  cbn [set_spill r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply].
  split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  split; [|split; [|split; [|split]]].
  - refine (conj C1 (conj C2 (conj _ (conj _ (conj _ _))))).
    + apply (srr_aval_keep_in rd rd' _ _ _ A_G_REC (A_G_REC + 960));
        [exact C3 | unfold OFF_NCALLS; lia | unfold OFF_NCALLS; lia | exact KR].
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HLc]. split; [|exact HLc].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (srr_acall_keep bl bl' rd rd'); [exact Hc | |].
      * intros x Hx. apply KR. unfold OFF_CALLS, CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KB. unfold lay_blocks. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + unfold acall_at. cbn [fst snd length].
      split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
      split; [exact BF|]. split; [exact BA|].
      split; [apply NoDup_ListNoDup; cbn [map]; constructor; [intros [] | constructor]|].
      intros k s0 pn Es Ep. destruct k as [|k]; [|cbn in Es; destruct k; discriminate].
      cbn in Es, Ep. injection Es as <-. injection Ep as <-. cbn [fst snd].
      split; [rewrite srr_add8_0; exact BP|].
      split; [exact Hp0|]. split; [exact Hbl|]. split; [lia|]. exact Hs.
    + constructor; [exact HL | constructor].
  - apply (srr_ans_keep bl bl' rd rd' _ _ _ HA).
    + intros x Hx. unfold OFF_ANSWER in Hx. apply KR; lia.
    + intros pn Hpn. apply KB. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left. exact Hpn.
  - apply (srr_rep_keep bl bl' rd rd' _ _ _ HY).
    + intros x Hx. unfold OFF_REPLY in Hx. apply KR; lia.
    + intros pn Hpn. apply KB. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact Hpn.
  - exact (srr_scalars_keep rd rd' A_G_REC R HX ltac:(intros x Hx; apply KR; lia)).
  - exact (srr_own_ins A_G_REC A_REC_SPILL Q _ (concat (l_calls Q))
             (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)) (p, Z.of_nat (length s) + 1)
             eq_refl (srr_lay_spill Q _ ES) HW (fun qn Hq => proj1 (proj2 (LV qn Hq)))
             ltac:(cbn [snd]; lia) (fun qn Hq => proj2 (AQ qn Hq)) AG AS).
Qed.

(* rec_calls_free's premises (lib/A/Prog/rec_calls_free_c.v:76-89) for ps = [l_spill Q] at c = A_REC_SPILL *)
Lemma sr_rcf_pre : forall (bl : list (Z * Z)) (rd : reader) (R : rstate) (Q : rlay),
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (forall i P, nth_error [l_spill Q] i = Some P ->
     (length P <= 6)%nat /\
     aval_mem rd (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length P)) /\
     forall a pn, nth_error P a = Some pn ->
       aval_mem rd (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\ In pn bl) /\
  NoDup (map fst (concat [l_spill Q])) /\
  length (concat [l_spill Q]) = length (snd (r_spill R)) /\
  (forall pn, In pn (l_spill Q) -> In pn (lay_blocks Q)).
Proof.
  intros bl rd R Q (S1 & S2 & S3 & HC & HA & HY & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6). destruct HW as [W1 W2].
  destruct C5 as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  split; [|split; [|split]].
  - intros i P EP. destruct i as [|i]; [|cbn in EP; destruct i; discriminate].
    cbn in EP. injection EP as <-.
    split; [rewrite F3; exact F2|].
    split.
    + rewrite F3. apply (srr_aval_addr rd (A_REC_SPILL + CALL_OFF_NARGS)); [unfold CALL_SIZE; lia | exact F5].
    + intros a pn Ea.
      assert (Ha : (a < length (snd (r_spill R)))%nat) by (rewrite <- F3; apply nth_error_Some; rewrite Ea; discriminate).
      destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
      destruct (F7 a s pn Es Ea) as (G1 & _ & G3 & _). split; [|exact G3].
      apply (srr_aval_addr rd (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a)); [unfold CALL_SIZE; lia | exact G1].
  - apply NoDup_ListNoDup in W1. apply NoDup_ListNoDup. cbn [concat]. rewrite app_nil_r.
    unfold lay_blocks in W1. rewrite !map_app in W1.
    apply List.NoDup_app_remove_l in W1. exact (List.NoDup_app_remove_r _ _ W1).
  - cbn [concat]. rewrite app_nil_r. exact F3.
  - intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
Qed.

(* the answer word: the old answer's block or 0 *)
Lemma sr_old : forall bl rd gr sc R Q, arep_at bl rd gr sc R Q ->
  aval_mem rd (gr + OFF_ANSWER) 8 (match l_answer Q with Some pn => fst pn | None => 0 end) /\
  (forall pa, l_answer Q = Some pa -> In pa (lay_blocks Q) /\ In pa bl /\ fst pa <> 0).
Proof.
  intros bl rd gr sc R Q (S1 & S2 & S3 & HC & HA & HY & HX & HW).
  revert HA. destruct (r_answer R) as [x|]; destruct (l_answer Q) as [qa|] eqn:EA;
    cbn [aanswer_at]; intros HA; try contradiction.
  - destruct HA as (N1 & N2 & N3 & _). split; [exact N1|]. intros pa Ea. injection Ea as <-.
    split; [|split; [exact N3 | exact N2]].
    unfold lay_blocks. rewrite EA. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    cbn [oblk In]. left. reflexivity.
  - split; [exact HA|]. intros pa Ea. discriminate.
Qed.

(* the spill's arguments dropped from the recorder's block set *)
Lemma sr_drop_spill : forall Q, NoDup (map fst (lay_blocks Q)) ->
  forall pn, In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) <->
    In pn (lay_blocks Q) /\ ~ In pn (l_spill Q).
Proof.
  intros Q H pn. unfold lay_blocks in *. split.
  - intros Hin. apply in_app_or in Hin as [Hin|Hin].
    + split; [apply in_or_app; left; exact Hin|]. intros Hs.
      apply (srr_nodup_fst_disj _ _ pn pn H Hin); [apply in_or_app; left; exact Hs | reflexivity].
    + split; [apply in_or_app; right; apply in_or_app; right; exact Hin|]. intros Hs.
      rewrite app_assoc in H.
      apply (srr_nodup_fst_disj _ _ pn pn H); [apply in_or_app; right; exact Hs | exact Hin | reflexivity].
  - intros [Hin Hs]. apply in_app_or in Hin as [Hin|Hin]; [apply in_or_app; left; exact Hin|].
    apply in_app_or in Hin as [Hin|Hin]; [contradiction | apply in_or_app; right; exact Hin].
Qed.

(* the table holds 16 calls exactly when the ncalls word is 16 *)
Lemma sr_ncalls : forall bl rd gr sc R Q, arep_at bl rd gr sc R Q ->
  aval_mem rd (gr + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R))) /\ (length (r_calls R) <= 16)%nat.
Proof.
  intros bl rd gr sc R Q (S1 & S2 & S3 & HC & _). destruct HC as (C1 & C2 & C3 & _).
  split; [exact C3 | exact C1].
Qed.

(* the recorder's representation carries over to a reader that keeps g_rec, record.spill and the recorder's blocks *)
Lemma sr_arep_keep : forall (bl bl' : list (Z * Z)) (rd rd' : reader) gr sc (R : rstate) (Q : rlay),
  arep_at bl rd gr sc R Q ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl') ->
  (forall a, (gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE) -> rd' a = rd a) ->
  (forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  arep_at bl' rd' gr sc R Q.
Proof.
  intros bl bl' rd rd' gr sc R Q (S1 & S2 & S3 & HC & HA & HY & HX & HW) KB0 KG KQ.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  assert (KB : forall pn, In pn (lay_blocks Q) -> In pn bl' /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
  { intros pn Hpn. split; [exact (KB0 pn Hpn) | intros i Hi; exact (KQ pn i Hpn Hi)]. }
  assert (KR : forall x, gr <= x < gr + 960 -> rd' x = rd x).
  { intros x Hx. apply KG. left. unfold REC_SIZE. exact Hx. }
  assert (KS : forall x, sc <= x < sc + 56 -> rd' x = rd x).
  { intros x Hx. apply KG. right. unfold SC_SIZE. exact Hx. }
  split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  split; [|split; [|split; [|split]]].
  - refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (srr_aval_keep_in rd rd' _ _ _ gr (gr + 960));
        [exact C3 | unfold OFF_NCALLS; lia | unfold OFF_NCALLS; lia | exact KR].
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HLc]. split; [|exact HLc].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (srr_acall_keep bl bl' rd rd'); [exact Hc | |].
      * intros x Hx. apply KR. unfold OFF_CALLS, CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KB. unfold lay_blocks. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + apply (srr_acall_keep bl bl' rd rd'); [exact C5 | |].
      * intros x Hx. unfold CALL_SIZE in Hx. apply KS. lia.
      * intros pn Hpn. apply KB. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - apply (srr_ans_keep bl bl' rd rd' _ _ _ HA).
    + intros x Hx. unfold OFF_ANSWER in Hx. apply KR; lia.
    + intros pn Hpn. apply KB. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left. exact Hpn.
  - apply (srr_rep_keep bl bl' rd rd' _ _ _ HY).
    + intros x Hx. unfold OFF_REPLY in Hx. apply KR; lia.
    + intros pn Hpn. apply KB. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact Hpn.
  - exact (srr_scalars_keep rd rd' gr R HX ltac:(intros x Hx; apply KR; lia)).
  - exact HW.
Qed.

(* record eta: a second spill write replaces the first *)
Lemma sr_set_spill2 : forall R c1 c2, set_spill (set_spill R c1) c2 = set_spill R c2.
Proof. intros R c1 c2. reflexivity. Qed.
