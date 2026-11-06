(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the model steps of sup_chain's inlined record(REC_CHAIN) and of its three
   argument appends (plugin-hostd/fuzz_command, ASan build, 0x8c2b4) over lib/A/Prog/CmdRep.v's rec_repA: the
   table arm (a new slot of g_rec.calls), the spill arm's fn/nargs stores after rec_calls_free, and one appended
   argument (arg_i's or arg_s's), each from the memory facts the walk proves; the keep lemmas are
   lib/Prog/RecInv.v's call_at_keep and rec_rep_frame over the ASan side's reader. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK15 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* the arguments a call holds in slot c: one live block per argument, its pointer in args[j], its text a C string
   of at most LMAX bytes filling the block exactly *)
Definition sc_newargs (rd : reader) (bl : list (Z * Z)) (c : Z) (A : list (list byte)) (P : list (Z * Z)) : Prop :=
  length P = length A /\ NoDup (map fst P) /\
  (forall j s pn, nth_error A j = Some s -> nth_error P j = Some pn ->
     aval_mem rd (c + CALL_OFF_ARGS + 8 * Z.of_nat j) 8 (fst pn) /\ fst pn <> 0 /\ In pn bl /\
     snd pn = Z.of_nat (length s) + 1 /\ Z.of_nat (length s) <= LMAX /\ astr_atR rd (fst pn) s).

Lemma sc_newargs_nil : forall rd bl c, sc_newargs rd bl c [] [].
Proof.
  intros rd bl c. split; [reflexivity|]. split; [constructor|].
  intros j s pn Ej. destruct j; cbn in Ej; discriminate Ej.
Qed.

(* the i-th element of a list, updated by f *)
Fixpoint sc_upd {T : Type} (i : nat) (f : T -> T) (l : list T) {struct l} : list T :=
  match l with
  | [] => []
  | a :: l' => match i with O => f a :: l' | S i' => a :: sc_upd i' f l' end
  end.

(* the recorder's state after one argument s is appended to a call: the i-th call of the table (Some i), or the
   spill (None) *)
Definition sc_push_arg (R : rstate) (k : option nat) (s : list byte) : rstate :=
  match k with
  | Some i => set_calls R (sc_upd i (fun d : rcall => (fst d, snd d ++ [s])) (r_calls R))
  | None => set_spill R (fst (r_spill R), snd (r_spill R) ++ [s])
  end.

(* the call e an append targets and its slot c *)
Definition sc_target (R : rstate) (k : option nat) (e : rcall) (c : Z) : Prop :=
  match k with
  | Some i => nth_error (r_calls R) i = Some e /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i
  | None => e = r_spill R /\ c = A_REC_SPILL
  end.

Lemma sc_upd_length : forall (T : Type) i (f : T -> T) l, length (sc_upd i f l) = length l.
Proof.
  intros T i f l. revert i. induction l as [|a l IH]; intros [|i]; cbn; [reflexivity | reflexivity | reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma sc_upd_nth_eq : forall (T : Type) i (f : T -> T) l, nth_error (sc_upd i f l) i = option_map f (nth_error l i).
Proof.
  intros T i f l. revert i. induction l as [|a l IH]; intros [|i]; cbn; [reflexivity | reflexivity | reflexivity |].
  exact (IH i).
Qed.

Lemma sc_upd_nth_ne : forall (T : Type) i j (f : T -> T) l, j <> i -> nth_error (sc_upd i f l) j = nth_error l j.
Proof.
  intros T i j f l. revert i j. induction l as [|a l IH]; intros [|i] [|j] Hne; cbn; try reflexivity.
  all: first [exfalso; lia | apply IH; lia].
Qed.

Lemma sc_upd_last : forall (T : Type) (f : T -> T) l y, sc_upd (length l) f (l ++ [y]) = l ++ [f y].
Proof. intros T f l y. induction l as [|a l IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma sc_nth_last : forall (T : Type) (l : list T) y, nth_error (l ++ [y]) (length l) = Some y.
Proof. intros T l y. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

(* the three appends after record(), against rec_record of the whole argument list *)
Lemma sc_push_arg_last : forall R cs fn A s,
  sc_push_arg (set_calls R (cs ++ [(fn, A)])) (Some (length cs)) s = set_calls R (cs ++ [(fn, A ++ [s])]).
Proof.
  intros R cs fn A s. unfold sc_push_arg, set_calls.
  cbn [r_refuse r_code r_calls r_spill r_answer r_nreplies r_reply r_state r_host].
  rewrite sc_upd_last. reflexivity.
Qed.

Lemma sc_push_arg_spill : forall R fn A s, sc_push_arg (set_spill R (fn, A)) None s = set_spill R (fn, A ++ [s]).
Proof. intros R fn A s. reflexivity. Qed.

Lemma sc_record3 : forall R fn a1 a2 a3, (length (r_calls R) < 16)%nat ->
  sc_push_arg (sc_push_arg (sc_push_arg (rec_record R fn []) (Some (length (r_calls R))) a1)
    (Some (length (r_calls R))) a2) (Some (length (r_calls R))) a3 = rec_record R fn [a1; a2; a3].
Proof.
  intros R fn a1 a2 a3 Hn. rewrite !(rec_record_calls R fn) by exact Hn. rewrite !sc_push_arg_last. reflexivity.
Qed.

Lemma sc_record3_spill : forall R fn a1 a2 a3, length (r_calls R) = 16%nat ->
  sc_push_arg (sc_push_arg (sc_push_arg (rec_record R fn []) None a1) None a2) None a3 = rec_record R fn [a1; a2; a3].
Proof. intros R fn a1 a2 a3 Hn. rewrite !(rec_record_spill R fn) by exact Hn. reflexivity. Qed.

Local Ltac sc3_lia :=
  unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, OFF_REFUSE, OFF_CODE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER,
    OFF_NREPLIES, OFF_REPLY, OFF_REPLY_SIZE, OFF_STATE, OFF_HOST, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS,
    CALL_OFF_ARGS, iv_apart in *; lia.

(* list facts *)
Lemma sc3_forall_in : forall (T : Type) (Pr : T -> Prop) l x, Forall Pr l -> In x l -> Pr x.
Proof.
  intros T Pr l x H. revert x. induction H as [|y l' Hy Hl IH]; intros x Hx; [destruct Hx|].
  destruct Hx as [<-|Hx]; [exact Hy | exact (IH x Hx)].
Qed.

Lemma sc3_perm_in : forall (l l' : list (Z * Z)) x, Permutation l l' -> In x l -> In x l'.
Proof. intros l l' x H Hx. eapply Permutation_in; eassumption. Qed.

(* the representation's NoDup is stdpp's (BvBase brings stdpp.base in); the list facts are proved over Stdlib's
   List.NoDup and carried over with stdpp.base.NoDup_ListNoDup *)
Lemma sc3_perm_nodup_fst : forall (l l' : list (Z * Z)), Permutation l l' -> NoDup (map fst l) -> NoDup (map fst l').
Proof.
  intros l l' H Hn. apply stdpp.base.NoDup_ListNoDup. apply stdpp.base.NoDup_ListNoDup in Hn.
  exact (Permutation_NoDup (Permutation_map fst H) Hn).
Qed.

Lemma sc3_nd_appL : forall (T : Type) (l1 l2 : list T),
  List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> List.NoDup (l1 ++ l2).
Proof.
  intros T l1 l2. induction l1 as [|a l1 IH]; intros H1 H2 D; cbn [app]; [exact H2|].
  apply List.NoDup_cons_iff in H1 as [Hna Hnd]. constructor.
  - intro Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hna Hin) | exact (D a (or_introl eq_refl) Hin)].
  - apply IH; [exact Hnd | exact H2 |]. intros x Hx. apply D. right. exact Hx.
Qed.

Lemma sc3_nd_app : forall (T : Type) (l1 l2 : list T),
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  intros T l1 l2 H1 H2 D. apply stdpp.base.NoDup_ListNoDup.
  apply stdpp.base.NoDup_ListNoDup in H1. apply stdpp.base.NoDup_ListNoDup in H2.
  exact (sc3_nd_appL T l1 l2 H1 H2 D).
Qed.

Lemma sc3_nd_snoc : forall (l : list (Z * Z)) p k, NoDup (map fst l) -> ~ In p (map fst l) ->
  NoDup (map fst (l ++ [(p, k)])).
Proof.
  intros l p k H N. apply stdpp.base.NoDup_ListNoDup. apply stdpp.base.NoDup_ListNoDup in H.
  rewrite map_app. cbn [map fst]. apply sc3_nd_appL; [exact H | constructor; [intros [] | constructor] |].
  intros x Hx [E|[]]. subst x. exact (N Hx).
Qed.

(* the recorder owns O ++ P after a step whose layout is the old one plus P *)
Lemma sc3_own_iff : forall O (Q Q' : rlay) P, (forall pn, In pn O <-> In pn (lay_blocks Q)) ->
  Permutation (lay_blocks Q') (lay_blocks Q ++ P) -> forall pn, In pn (O ++ P) <-> In pn (lay_blocks Q').
Proof.
  intros O Q Q' P HO Hperm pn. split; intros H.
  - apply (sc3_perm_in (lay_blocks Q ++ P)); [apply Permutation_sym; exact Hperm|].
    apply in_app_or in H as [H|H]; apply in_or_app; [left; exact (proj1 (HO pn) H) | right; exact H].
  - apply (sc3_perm_in _ _ _ Hperm) in H.
    apply in_app_or in H as [H|H]; apply in_or_app; [left; exact (proj2 (HO pn) H) | right; exact H].
Qed.

(* the layouts after each step, against the old one *)
Lemma sc3_lay_slot_perm : forall Q P,
  Permutation (lay_blocks (RLay (l_calls Q ++ [P]) (l_spill Q) (l_answer Q) (l_reply Q))) (lay_blocks Q ++ P).
Proof.
  intros Q P. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
  rewrite concat_app. cbn [concat]. rewrite app_nil_r.
  set (X := concat (l_calls Q)). set (T := l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)).
  rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
Qed.

Lemma sc3_concat_upd_perm : forall (L : list (list (Z * Z))) i x, (i < length L)%nat ->
  Permutation (concat (sc_upd i (fun P => P ++ [x]) L)) (concat L ++ [x]).
Proof.
  intros L. induction L as [|P L IH]; intros i x Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [sc_upd concat].
  - rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
  - rewrite <- app_assoc. apply Permutation_app_head. apply IH. lia.
Qed.

Lemma sc3_lay_push_tab_perm : forall Q i x, (i < length (l_calls Q))%nat ->
  Permutation (lay_blocks (RLay (sc_upd i (fun P => P ++ [x]) (l_calls Q)) (l_spill Q) (l_answer Q) (l_reply Q)))
              (lay_blocks Q ++ [x]).
Proof.
  intros Q i x Hi. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
  set (T := l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)).
  eapply perm_trans; [apply Permutation_app_tail; exact (sc3_concat_upd_perm (l_calls Q) i x Hi)|].
  rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
Qed.

Lemma sc3_lay_push_spill_perm : forall Q x,
  Permutation (lay_blocks (RLay (l_calls Q) (l_spill Q ++ [x]) (l_answer Q) (l_reply Q))) (lay_blocks Q ++ [x]).
Proof.
  intros Q x. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
  set (X := concat (l_calls Q)). set (T := oblk (l_answer Q) ++ oblk (l_reply Q)).
  rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm.
Qed.

(* the keep lemmas: RecInv.v's bytes_at_keep / call_at_keep and rec_rep_frame's parts, over the reader *)
Lemma sc3_aval_keep : forall rd rd' a n v, aval_mem rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma sc3_bytes_keep : forall rd rd' p l, abytes_atR rd p l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> rd' (p + i) = rd (p + i)) -> abytes_atR rd' p l.
Proof. intros rd rd' p l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma sc3_str_keep : forall rd rd' p s, astr_atR rd p s ->
  (forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H1 H2] K. split; [|exact H2].
  apply (sc3_bytes_keep rd); [exact H1|]. intros i Hi. apply K. rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.

Lemma sc3_call_keep : forall bl bl' rd rd' a c P, acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl -> In pn bl') ->
  (forall pn, In pn P -> forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk) K KB KP.
  unfold acall_at.
  split; [exact Hfn|]. split; [exact Hn|]. split; [exact Hl|].
  split; [apply (sc3_aval_keep rd); [exact Hb0 | intros x Hx; apply K; unfold CALL_SIZE, CALL_OFF_FN in *; lia]|].
  split; [apply (sc3_aval_keep rd); [exact Hb1 | intros x Hx; apply K; unfold CALL_SIZE, CALL_OFF_NARGS in *; lia]|].
  split; [exact Hnd|].
  intros k s pn Es Ep. destruct (Hk k s pn Es Ep) as (Hs & Hp0 & Hin & Hsz & Hstr).
  assert (Hkl : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  pose proof (nth_error_In P k Ep) as HinP.
  split; [apply (sc3_aval_keep rd); [exact Hs | intros x Hx; apply K; unfold CALL_SIZE, CALL_OFF_ARGS in *; lia]|].
  split; [exact Hp0|]. split; [exact (KB pn HinP Hin)|]. split; [exact Hsz|].
  apply (sc3_str_keep rd); [exact Hstr|]. intros i Hi. apply (KP pn HinP). lia.
Qed.

Lemma sc3_answer_keep : forall bl bl' rd rd' gr t q, aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl -> In pn bl') ->
  (forall pn, In pn (oblk q) -> forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q H K KB KP. unfold aanswer_at in H |- *.
  destruct t as [x|]; destruct q as [pn|]; cbv beta iota in H |- *; try contradiction.
  - destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
    assert (Hq : In pn (oblk (Some pn))) by (left; reflexivity).
    split; [apply (sc3_aval_keep rd); [exact N1 | intros y Hy; apply K; lia]|].
    split; [exact N2|]. split; [exact (KB pn Hq N3)|]. split; [exact N4|]. split; [|exact N6].
    apply (sc3_str_keep rd); [exact N5|]. intros i Hi. apply (KP pn Hq). lia.
  - apply (sc3_aval_keep rd); [exact H | intros y Hy; apply K; lia].
Qed.

Lemma sc3_reply_keep : forall bl bl' rd rd' gr y q, areply_at bl rd gr y q ->
  (forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY_SIZE + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl -> In pn bl') ->
  (forall pn, In pn (oblk q) -> forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  areply_at bl' rd' gr y q.
Proof.
  intros bl bl' rd rd' gr y q H K KB KP. unfold areply_at in H |- *.
  destruct y as [x|]; destruct q as [pn|]; cbv beta iota in H |- *; try contradiction.
  - destruct H as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    assert (Hq : In pn (oblk (Some pn))) by (left; reflexivity).
    split; [apply (sc3_aval_keep rd); [exact P1 | intros z Hz; apply K; unfold OFF_REPLY, OFF_REPLY_SIZE in *; lia]|].
    split; [apply (sc3_aval_keep rd); [exact P2 | intros z Hz; apply K; unfold OFF_REPLY, OFF_REPLY_SIZE in *; lia]|].
    split; [exact P3|]. split; [exact P4|]. split; [exact (KB pn Hq P5)|]. split; [exact P6|]. split; [|exact P8].
    apply (sc3_bytes_keep rd); [exact P7|]. intros i Hi. apply (KP pn Hq). lia.
  - destruct H as [P1 P2].
    split; [apply (sc3_aval_keep rd); [exact P1 | intros z Hz; apply K; unfold OFF_REPLY, OFF_REPLY_SIZE in *; lia]|].
    apply (sc3_aval_keep rd); [exact P2 | intros z Hz; apply K; unfold OFF_REPLY, OFF_REPLY_SIZE in *; lia].
Qed.

Lemma sc3_scalars_keep : forall rd rd' gr R, ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + OFF_NREPLIES <= x < gr + OFF_NREPLIES + 4 \/
             gr + OFF_STATE <= x < gr + OFF_HOST + 8 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R (X1 & X2 & X3 & X4 & X5 & X6) K. unfold ag1_scalars.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  all: apply (sc3_aval_keep rd); [eassumption | intros x Hx; apply K;
    unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *; lia].
Qed.

(* the call e of slot a with one more argument s in the block (p, |s| + 1) *)
Lemma sc3_call_push : forall bl bl' rd rd' a c P s p,
  acall_at bl rd a c P -> Forall (fun t => Z.of_nat (length t) <= LMAX) (snd c) ->
  (length (snd c) < 6)%nat ->
  (forall y, a <= y < a + CALL_SIZE -> ~ (a + CALL_OFF_NARGS <= y < a + CALL_OFF_NARGS + 4) ->
     ~ (a + CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) <= y <
        a + CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) + 8) -> rd' y = rd y) ->
  (forall pn, In pn P -> In pn bl -> In pn bl') ->
  (forall pn, In pn P -> forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  ~ In p (map fst P) ->
  aval_mem rd' (a + CALL_OFF_NARGS) 4 (Z.of_nat (length (snd c)) + 1) ->
  aval_mem rd' (a + CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c))) 8 p ->
  astr_atR rd' p s -> Z.of_nat (length s) <= LMAX -> p <> 0 -> In (p, Z.of_nat (length s) + 1) bl' ->
  acall_at bl' rd' a (fst c, snd c ++ [s]) (P ++ [(p, Z.of_nat (length s) + 1)]) /\
  Forall (fun t => Z.of_nat (length t) <= LMAX) (snd c ++ [s]).
Proof.
  intros bl bl' rd rd' a c P s p (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk) HF Hm K KB KP Hx Hna Hpa Hs HsL Hp0 Hin.
  split.
  - unfold acall_at. cbn [fst snd].
    split; [exact Hfn|].
    split; [rewrite length_app; cbn [length]; lia|].
    split; [rewrite !length_app, Hl; reflexivity|].
    split; [apply (sc3_aval_keep rd); [exact Hb0 | intros y Hy; apply K;
      unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia]|].
    split.
    { rewrite length_app. cbn [length].
      replace (Z.of_nat (length (snd c) + 1)) with (Z.of_nat (length (snd c)) + 1) by lia. exact Hna. }
    split.
    { exact (sc3_nd_snoc P p _ Hnd Hx). }
    intros k t pn Et Ep. destruct (Nat.lt_ge_cases k (length (snd c))) as [Hk'|Hk'].
    + rewrite nth_error_app1 in Et by exact Hk'. rewrite nth_error_app1 in Ep by lia.
      destruct (Hk k t pn Et Ep) as (H1 & H2 & H3 & H4 & H5).
      pose proof (nth_error_In P k Ep) as HinP.
      split; [apply (sc3_aval_keep rd); [exact H1 | intros y Hy; apply K;
        unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia]|].
      split; [exact H2|]. split; [exact (KB pn HinP H3)|]. split; [exact H4|].
      apply (sc3_str_keep rd); [exact H5|]. intros i Hi. apply (KP pn HinP). lia.
    + assert (Ek : k = length (snd c) \/ (length (snd c) < k)%nat) by lia.
      destruct Ek as [->|Hgt].
      * rewrite nth_error_app2, Nat.sub_diag in Et by lia. rewrite nth_error_app2 in Ep by lia.
        rewrite Hl, Nat.sub_diag in Ep. cbn in Et, Ep. injection Et as <-. injection Ep as <-. cbn [fst snd].
        split; [exact Hpa|]. split; [exact Hp0|]. split; [exact Hin|]. split; [lia | exact Hs].
      * exfalso. rewrite nth_error_app2 in Et by lia.
        assert (Hnone : nth_error [s] (k - length (snd c)) = None) by (apply nth_error_None; cbn [length]; lia).
        rewrite Hnone in Et. discriminate Et.
  - apply List.Forall_forall. intros t Ht. apply in_app_or in Ht as [Ht|[<-|[]]].
    + exact (sc3_forall_in _ _ _ _ HF Ht).
    + exact HsL.
Qed.

(* the new call in slot c (record()'s table arm with its arguments already in place) *)
Lemma sc3_newcall : forall bl rd c fn A P,
  0 <= fn < REC_FN_COUNT -> (length A <= 6)%nat ->
  aval_mem rd (c + CALL_OFF_FN) 4 fn ->
  aval_mem rd (c + CALL_OFF_NARGS) 4 (Z.of_nat (length A)) ->
  sc_newargs rd bl c A P ->
  acall_at bl rd c (fn, A) P /\ Forall (fun s => Z.of_nat (length s) <= LMAX) A.
Proof.
  intros bl rd c fn A P Hfn HA Hf Hna (HPl & HPnd & HPk). split.
  - unfold acall_at. cbn [fst snd].
    split; [exact Hfn|]. split; [exact HA|]. split; [exact HPl|]. split; [exact Hf|]. split; [exact Hna|].
    split; [exact HPnd|].
    intros k s pn Es Ep. destruct (HPk k s pn Es Ep) as (H1 & H2 & H3 & H4 & H5 & H6).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [lia | exact H6].
  - apply List.Forall_forall. intros s Hs. apply In_nth_error in Hs as [j Ej].
    destruct (nth_error P j) as [pn|] eqn:Ep.
    + destruct (HPk j s pn Ej Ep) as (_ & _ & _ & _ & H5 & _). exact H5.
    + exfalso. apply nth_error_None in Ep.
      assert (Hj : (j < length A)%nat) by (apply nth_error_Some; rewrite Ej; discriminate). lia.
Qed.

(* record()'s table arm over arep_at: g_rec.ncalls and slot c written, every other byte of g_rec and record.spill
   and every byte of the recorder's blocks kept *)
Lemma sc3_arep_slot : forall bl bl' rd rd' R Q P c fn A,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (length (r_calls R) < 16)%nat ->
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
  (length A <= 6)%nat -> 0 <= fn < REC_FN_COUNT ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl -> In pn bl') ->
  (forall pn, In pn (lay_blocks Q) -> forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  (forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
     ~ (c <= a < c + CALL_SIZE) -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rd' a = rd a) ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
  aval_mem rd' (c + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 (Z.of_nat (length A)) ->
  sc_newargs rd' bl' c A P ->
  Forall (fun pn => iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\
                    iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE) P ->
  (forall pn, In pn (lay_blocks Q) -> ~ In (fst pn) (map fst P)) ->
  arep_at bl' rd' A_G_REC A_REC_SPILL (set_calls R (r_calls R ++ [(fn, A)]))
    (RLay (l_calls Q ++ [P]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
  intros bl bl' rd rd' R Q P c fn A HR Hn Hc HA Hfn TB TK TG Hnc Hf Hna HP HPa HPd.
  subst c.
  destruct (sc3_newcall bl' rd' _ fn A P Hfn HA Hf Hna HP) as [Hnew HnewL].
  destruct HP as (HPl & HPnd & _).
  destruct HR as (Hg8 & Hs8 & Hgs & HC & HAn & HRe & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6). destruct HW as [HW1 HW2].
  pose proof (sc3_lay_slot_perm Q P) as Hperm.
  assert (Ls : forall pn, In pn (l_spill Q) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
  assert (La : forall pn, In pn (oblk (l_answer Q)) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hpn. }
  assert (Lr : forall pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
    exact Hpn. }
  assert (HA' : aanswer_at bl' rd' A_G_REC (r_answer R) (l_answer Q)).
  { apply (sc3_answer_keep bl bl' rd rd' _ _ _ HAn).
    - intros x Hx. apply TG; sc3_lia.
    - intros pn Hpn. exact (TB pn (La pn Hpn)).
    - intros pn Hpn. exact (TK pn (La pn Hpn)). }
  assert (HR' : areply_at bl' rd' A_G_REC (r_reply R) (l_reply Q)).
  { apply (sc3_reply_keep bl bl' rd rd' _ _ _ HRe).
    - intros x Hx. apply TG; sc3_lia.
    - intros pn Hpn. exact (TB pn (Lr pn Hpn)).
    - intros pn Hpn. exact (TK pn (Lr pn Hpn)). }
  assert (HX' : ag1_scalars rd' A_G_REC R).
  { apply (sc3_scalars_keep rd rd' _ _ HX). intros x Hx. apply TG; sc3_lia. }
  unfold arep_at. refine (conj Hg8 (conj Hs8 (conj Hgs (conj _ (conj HA' (conj HR' (conj HX' _))))))).
  - unfold ag1_calls, set_calls. cbn [r_calls r_spill l_calls l_spill].
    split; [rewrite length_app; cbn [length]; lia|].
    split; [rewrite !length_app, C2; reflexivity|].
    split.
    { rewrite length_app. cbn [length].
      replace (Z.of_nat (length (r_calls R) + 1)) with (Z.of_nat (length (r_calls R)) + 1) by lia. exact Hnc. }
    split.
    { intros i c0 P0 E1 E2. destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      - rewrite nth_error_app1 in E1 by exact Hi. rewrite nth_error_app1 in E2 by lia.
        destruct (C4 i c0 P0 E1 E2) as [Hc0 HL]. split; [|exact HL].
        assert (HinP : forall pn, In pn P0 -> In pn (lay_blocks Q)).
        { intros pn Hpn. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P0.
          split; [exact (nth_error_In (l_calls Q) i E2) | exact Hpn]. }
        apply (sc3_call_keep bl bl' rd rd' _ c0 P0 Hc0).
        + intros x Hx. apply TG; sc3_lia.
        + intros pn Hpn. exact (TB pn (HinP pn Hpn)).
        + intros pn Hpn. exact (TK pn (HinP pn Hpn)).
      - assert (Ei : i = length (r_calls R) \/ (length (r_calls R) < i)%nat) by lia.
        destruct Ei as [->|Hgt].
        + rewrite nth_error_app2 in E1 by lia. rewrite nth_error_app2 in E2 by lia.
          rewrite C2, Nat.sub_diag in E2. rewrite Nat.sub_diag in E1. cbn in E1, E2.
          injection E1 as <-. injection E2 as <-. exact (conj Hnew HnewL).
        + exfalso. rewrite nth_error_app2 in E1 by lia. revert E1.
          destruct (i - length (r_calls R))%nat as [|d] eqn:Ed; intros E1; [lia|].
          destruct d; cbn in E1; discriminate E1. }
    split; [|exact C6].
    apply (sc3_call_keep bl bl' rd rd' _ _ _ C5).
    + intros x Hx. apply TG; sc3_lia.
    + intros pn Hpn. exact (TB pn (Ls pn Hpn)).
    + intros pn Hpn. exact (TK pn (Ls pn Hpn)).
  - unfold ag1_own. split.
    + apply (sc3_perm_nodup_fst (lay_blocks Q ++ P)); [apply Permutation_sym; exact Hperm|].
      rewrite map_app. apply sc3_nd_app; [exact HW1 | exact HPnd |].
      intros a Ha Hb. apply in_map_iff in Ha as (pn & Ea & Hpn). subst a. exact (HPd pn Hpn Hb).
    + intros pn Hpn. apply (sc3_perm_in _ _ _ Hperm) in Hpn. apply in_app_or in Hpn as [Hpn|Hpn].
      * exact (HW2 pn Hpn).
      * exact (sc3_forall_in _ _ _ _ HPa Hpn).
Qed.

(* record()'s spill arm after rec_calls_free, over arep_at: record.spill's fn and nargs words written, every
   other byte of g_rec and record.spill and every byte of the recorder's blocks kept *)
Lemma sc3_arep_spill_fn : forall bl rd rd' R Q fn,
  arep_at bl rd A_G_REC A_REC_SPILL R Q -> snd (r_spill R) = [] ->
  0 <= fn < REC_FN_COUNT ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
  (forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
     ~ (A_REC_SPILL + CALL_OFF_FN <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) -> rd' a = rd a) ->
  (forall pn, In pn (lay_blocks Q) -> forall j, 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
  arep_at bl rd' A_G_REC A_REC_SPILL (set_spill R (fn, [])) Q.
Proof.
  intros bl rd rd' R Q fn HR Hsp Hfn Hf Hn0 TG TK.
  destruct HR as (Hg8 & Hs8 & Hgs & HC & HAn & HRe & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  assert (La : forall pn, In pn (oblk (l_answer Q)) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hpn. }
  assert (Lr : forall pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
    exact Hpn. }
  assert (HA' : aanswer_at bl rd' A_G_REC (r_answer R) (l_answer Q)).
  { apply (sc3_answer_keep bl bl rd rd' _ _ _ HAn).
    - intros x Hx. apply TG; sc3_lia.
    - intros pn _ Hb. exact Hb.
    - intros pn Hpn. exact (TK pn (La pn Hpn)). }
  assert (HR' : areply_at bl rd' A_G_REC (r_reply R) (l_reply Q)).
  { apply (sc3_reply_keep bl bl rd rd' _ _ _ HRe).
    - intros x Hx. apply TG; sc3_lia.
    - intros pn _ Hb. exact Hb.
    - intros pn Hpn. exact (TK pn (Lr pn Hpn)). }
  assert (HX' : ag1_scalars rd' A_G_REC R).
  { apply (sc3_scalars_keep rd rd' _ _ HX). intros x Hx. apply TG; sc3_lia. }
  unfold arep_at. refine (conj Hg8 (conj Hs8 (conj Hgs (conj _ (conj HA' (conj HR' (conj HX' HW))))))).
  unfold ag1_calls, set_spill. cbn [r_calls r_spill l_calls l_spill].
  split; [exact C1|]. split; [exact C2|].
  split; [apply (sc3_aval_keep rd); [exact C3 | intros x Hx; apply TG; sc3_lia]|].
  split.
  { intros i c0 P0 E1 E2. destruct (C4 i c0 P0 E1 E2) as [Hc0 HL]. split; [|exact HL].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite E1; discriminate).
    apply (sc3_call_keep bl bl rd rd' _ c0 P0 Hc0).
    - intros x Hx. apply TG; sc3_lia.
    - intros pn _ Hb. exact Hb.
    - intros pn Hpn. apply TK. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P0.
      split; [exact (nth_error_In (l_calls Q) i E2) | exact Hpn]. }
  split.
  - destruct C5 as (_ & _ & Hl & _ & _ & Hnd & _). rewrite Hsp in Hl. unfold acall_at. cbn [fst snd].
    split; [exact Hfn|]. split; [cbn [length]; lia|]. split; [exact Hl|]. split; [exact Hf|].
    split; [exact Hn0|]. split; [exact Hnd|].
    intros k t pn Et. destruct k; cbn in Et; discriminate Et.
  - cbn [snd]. constructor.
Qed.

(* one appended argument over arep_at, for a call of the table *)
Lemma sc3_arep_push_tab : forall bl bl' rd rd' R Q i e c s p,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  nth_error (r_calls R) i = Some e ->
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i ->
  (length (snd e) < 6)%nat ->
  (forall pn, In pn bl -> In pn bl') ->
  (forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
     ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
     ~ (c + CALL_OFF_ARGS + 8 * Z.of_nat (length (snd e)) <= a <
        c + CALL_OFF_ARGS + 8 * Z.of_nat (length (snd e)) + 8) -> rd' a = rd a) ->
  (forall pn, In pn (lay_blocks Q) -> forall j, 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 (Z.of_nat (length (snd e)) + 1) ->
  aval_mem rd' (c + CALL_OFF_ARGS + 8 * Z.of_nat (length (snd e))) 8 p ->
  astr_atR rd' p s -> Z.of_nat (length s) <= LMAX -> p <> 0 ->
  In (p, Z.of_nat (length s) + 1) bl' ->
  iv_apart p (Z.of_nat (length s) + 1) A_G_REC REC_SIZE ->
  iv_apart p (Z.of_nat (length s) + 1) A_REC_SPILL SC_SIZE ->
  ~ In p (map fst (lay_blocks Q)) ->
  arep_at bl' rd' A_G_REC A_REC_SPILL
    (set_calls R (sc_upd i (fun d : rcall => (fst d, snd d ++ [s])) (r_calls R)))
    (RLay (sc_upd i (fun P => P ++ [(p, Z.of_nat (length s) + 1)]) (l_calls Q)) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
  intros bl bl' rd rd' R Q i e c s p HR Ei Hc Hm TB TG TK Hna Hpa Hs HsL Hp0 Hin Hag Has Hfr.
  subst c.
  destruct HR as (Hg8 & Hs8 & Hgs & HC & HAn & HRe & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6). destruct HW as [HW1 HW2].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ei; discriminate).
  destruct (nth_error (l_calls Q) i) as [Pi|] eqn:EPi; [|exfalso; apply nth_error_None in EPi; lia].
  destruct (C4 i e Pi Ei EPi) as [HcI HLI].
  assert (Lc : forall P0 pn, In P0 (l_calls Q) -> In pn P0 -> In pn (lay_blocks Q)).
  { intros P0 pn H0 Hpn. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P0.
    split; [exact H0 | exact Hpn]. }
  assert (Ls : forall pn, In pn (l_spill Q) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
  assert (La : forall pn, In pn (oblk (l_answer Q)) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hpn. }
  assert (Lr : forall pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
    exact Hpn. }
  assert (HA' : aanswer_at bl' rd' A_G_REC (r_answer R) (l_answer Q)).
  { apply (sc3_answer_keep bl bl' rd rd' _ _ _ HAn).
    - intros x Hx. apply TG; sc3_lia.
    - intros pn _ Hb. exact (TB pn Hb).
    - intros pn Hpn. exact (TK pn (La pn Hpn)). }
  assert (HR' : areply_at bl' rd' A_G_REC (r_reply R) (l_reply Q)).
  { apply (sc3_reply_keep bl bl' rd rd' _ _ _ HRe).
    - intros x Hx. apply TG; sc3_lia.
    - intros pn _ Hb. exact (TB pn Hb).
    - intros pn Hpn. exact (TK pn (Lr pn Hpn)). }
  assert (HX' : ag1_scalars rd' A_G_REC R).
  { apply (sc3_scalars_keep rd rd' _ _ HX). intros x Hx. apply TG; sc3_lia. }
  assert (HiQ : (i < length (l_calls Q))%nat) by lia.
  pose proof (sc3_lay_push_tab_perm Q i (p, Z.of_nat (length s) + 1) HiQ) as Hperm.
  unfold arep_at. refine (conj Hg8 (conj Hs8 (conj Hgs (conj _ (conj HA' (conj HR' (conj HX' _))))))).
  - unfold ag1_calls, set_calls. cbn [r_calls r_spill l_calls l_spill].
    split; [rewrite sc_upd_length; exact C1|].
    split; [rewrite !sc_upd_length; exact C2|].
    split; [rewrite sc_upd_length; apply (sc3_aval_keep rd); [exact C3 | intros y Hy; apply TG; sc3_lia]|].
    split.
    { intros j c0 P0 E1 E2. destruct (Nat.eq_dec j i) as [->|Hji].
      - rewrite sc_upd_nth_eq, Ei in E1. rewrite sc_upd_nth_eq, EPi in E2. cbn in E1, E2.
        injection E1 as <-. injection E2 as <-. cbn [fst snd].
        refine (sc3_call_push bl bl' rd rd' _ e Pi s p HcI HLI Hm _ _ _ _ Hna Hpa Hs HsL Hp0 Hin).
        + intros y Hy H1 H2. apply TG; [sc3_lia | exact H1 | exact H2].
        + intros pn _ Hb. exact (TB pn Hb).
        + intros pn Hpn. exact (TK pn (Lc Pi pn (nth_error_In (l_calls Q) i EPi) Hpn)).
        + intro Hp. apply Hfr. apply in_map_iff in Hp as (pn & Ep & Hpn). subst p. apply in_map.
          exact (Lc Pi pn (nth_error_In (l_calls Q) i EPi) Hpn).
      - rewrite (sc_upd_nth_ne _ i j) in E1 by exact Hji. rewrite (sc_upd_nth_ne _ i j) in E2 by exact Hji.
        destruct (C4 j c0 P0 E1 E2) as [Hc0 HL]. split; [|exact HL].
        assert (Hj : (j < length (r_calls R))%nat) by (apply nth_error_Some; rewrite E1; discriminate).
        apply (sc3_call_keep bl bl' rd rd' _ c0 P0 Hc0).
        + intros y Hy. apply TG; sc3_lia.
        + intros pn _ Hb. exact (TB pn Hb).
        + intros pn Hpn. exact (TK pn (Lc P0 pn (nth_error_In (l_calls Q) j E2) Hpn)). }
    split; [|exact C6].
    apply (sc3_call_keep bl bl' rd rd' _ _ _ C5).
    + intros y Hy. apply TG; sc3_lia.
    + intros pn _ Hb. exact (TB pn Hb).
    + intros pn Hpn. exact (TK pn (Ls pn Hpn)).
  - unfold ag1_own. split.
    + apply (sc3_perm_nodup_fst (lay_blocks Q ++ [(p, Z.of_nat (length s) + 1)]));
        [apply Permutation_sym; exact Hperm|].
      exact (sc3_nd_snoc _ p _ HW1 Hfr).
    + intros pn Hpn. apply (sc3_perm_in _ _ _ Hperm) in Hpn. apply in_app_or in Hpn as [Hpn|[<-|[]]].
      * exact (HW2 pn Hpn).
      * cbn [fst snd]. split; [exact Hag | exact Has].
Qed.

(* one appended argument over arep_at, for record.spill *)
Lemma sc3_arep_push_spill : forall bl bl' rd rd' R Q c s p,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  c = A_REC_SPILL ->
  (length (snd (r_spill R)) < 6)%nat ->
  (forall pn, In pn bl -> In pn bl') ->
  (forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
     ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
     ~ (c + CALL_OFF_ARGS + 8 * Z.of_nat (length (snd (r_spill R))) <= a <
        c + CALL_OFF_ARGS + 8 * Z.of_nat (length (snd (r_spill R))) + 8) -> rd' a = rd a) ->
  (forall pn, In pn (lay_blocks Q) -> forall j, 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 (Z.of_nat (length (snd (r_spill R))) + 1) ->
  aval_mem rd' (c + CALL_OFF_ARGS + 8 * Z.of_nat (length (snd (r_spill R)))) 8 p ->
  astr_atR rd' p s -> Z.of_nat (length s) <= LMAX -> p <> 0 ->
  In (p, Z.of_nat (length s) + 1) bl' ->
  iv_apart p (Z.of_nat (length s) + 1) A_G_REC REC_SIZE ->
  iv_apart p (Z.of_nat (length s) + 1) A_REC_SPILL SC_SIZE ->
  ~ In p (map fst (lay_blocks Q)) ->
  arep_at bl' rd' A_G_REC A_REC_SPILL (set_spill R (fst (r_spill R), snd (r_spill R) ++ [s]))
    (RLay (l_calls Q) (l_spill Q ++ [(p, Z.of_nat (length s) + 1)]) (l_answer Q) (l_reply Q)).
Proof.
  intros bl bl' rd rd' R Q c s p HR Hc Hm TB TG TK Hna Hpa Hs HsL Hp0 Hin Hag Has Hfr.
  subst c.
  destruct HR as (Hg8 & Hs8 & Hgs & HC & HAn & HRe & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6). destruct HW as [HW1 HW2].
  assert (Lc : forall P0 pn, In P0 (l_calls Q) -> In pn P0 -> In pn (lay_blocks Q)).
  { intros P0 pn H0 Hpn. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P0.
    split; [exact H0 | exact Hpn]. }
  assert (Ls : forall pn, In pn (l_spill Q) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
  assert (La : forall pn, In pn (oblk (l_answer Q)) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hpn. }
  assert (Lr : forall pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
    exact Hpn. }
  assert (HA' : aanswer_at bl' rd' A_G_REC (r_answer R) (l_answer Q)).
  { apply (sc3_answer_keep bl bl' rd rd' _ _ _ HAn).
    - intros x Hx. apply TG; sc3_lia.
    - intros pn _ Hb. exact (TB pn Hb).
    - intros pn Hpn. exact (TK pn (La pn Hpn)). }
  assert (HR' : areply_at bl' rd' A_G_REC (r_reply R) (l_reply Q)).
  { apply (sc3_reply_keep bl bl' rd rd' _ _ _ HRe).
    - intros x Hx. apply TG; sc3_lia.
    - intros pn _ Hb. exact (TB pn Hb).
    - intros pn Hpn. exact (TK pn (Lr pn Hpn)). }
  assert (HX' : ag1_scalars rd' A_G_REC R).
  { apply (sc3_scalars_keep rd rd' _ _ HX). intros x Hx. apply TG; sc3_lia. }
  pose proof (sc3_lay_push_spill_perm Q (p, Z.of_nat (length s) + 1)) as Hperm.
  unfold arep_at. refine (conj Hg8 (conj Hs8 (conj Hgs (conj _ (conj HA' (conj HR' (conj HX' _))))))).
  - unfold ag1_calls, set_spill. cbn [r_calls r_spill l_calls l_spill]. cbn [fst snd].
    split; [exact C1|]. split; [exact C2|].
    split; [apply (sc3_aval_keep rd); [exact C3 | intros y Hy; apply TG; sc3_lia]|].
    split.
    { intros j c0 P0 E1 E2. destruct (C4 j c0 P0 E1 E2) as [Hc0 HL]. split; [|exact HL].
      assert (Hj : (j < length (r_calls R))%nat) by (apply nth_error_Some; rewrite E1; discriminate).
      apply (sc3_call_keep bl bl' rd rd' _ c0 P0 Hc0).
      + intros y Hy. apply TG; sc3_lia.
      + intros pn _ Hb. exact (TB pn Hb).
      + intros pn Hpn. exact (TK pn (Lc P0 pn (nth_error_In (l_calls Q) j E2) Hpn)). }
    refine (sc3_call_push bl bl' rd rd' _ (r_spill R) (l_spill Q) s p C5 C6 Hm _ _ _ _ Hna Hpa Hs HsL Hp0 Hin).
    + intros y Hy H1 H2. apply TG; [sc3_lia | exact H1 | exact H2].
    + intros pn _ Hb. exact (TB pn Hb).
    + intros pn Hpn. exact (TK pn (Ls pn Hpn)).
    + intro Hp. apply Hfr. apply in_map_iff in Hp as (pn & Ep & Hpn). subst p. apply in_map. exact (Ls pn Hpn).
  - unfold ag1_own. split.
    + apply (sc3_perm_nodup_fst (lay_blocks Q ++ [(p, Z.of_nat (length s) + 1)]));
        [apply Permutation_sym; exact Hperm|].
      exact (sc3_nd_snoc _ p _ HW1 Hfr).
    + intros pn Hpn. apply (sc3_perm_in _ _ _ Hperm) in Hpn. apply in_app_or in Hpn as [Hpn|[<-|[]]].
      * exact (HW2 pn Hpn).
      * cbn [fst snd]. split; [exact Hag | exact Has].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable B : asyms.

(* what the recorder's state says before record() picks a slot: at most 16 calls, their count in g_rec.ncalls,
   and every block the recorder owns live *)
Lemma scA_slot_in : forall ly S rd R O, rec_repA B ly S rd R O -> (length (r_calls R) <= 16)%nat.
Proof. intros ly S rd R O (Q & (_ & _ & _ & (C1 & _) & _) & _). exact C1. Qed.

Lemma scA_ncalls_at : forall ly S rd R O, rec_repA B ly S rd R O ->
  aval_mem rd (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R))).
Proof. intros ly S rd R O (Q & (_ & _ & _ & (_ & _ & C3 & _) & _) & _). exact C3. Qed.

Lemma scA_own_live : forall ly S rd R O, rec_repA B ly S rd R O ->
  forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
  intros ly S rd R O (Q & HQ & HO) pn Hpn. exact (lay_blocks_in _ _ _ _ _ _ HQ pn (proj1 (HO pn) Hpn)).
Qed.

(* record()'s table arm (length (r_calls R) < 16) with the call's arguments in place, framed: the walk's
   agreement on g_rec and record.spill outside the slot and g_rec.ncalls, and on the bytes of the recorder's
   blocks O *)
Lemma scA_record_slot_fr : forall ly S ly' S' rd rd' R O P c A fn,
  rec_repA B ly S rd R O ->
  (length (r_calls R) < 16)%nat ->
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
  (length A <= 6)%nat -> 0 <= fn < REC_FN_COUNT ->
  (forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly' S')) ->
  (forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
     ~ (c <= a < c + CALL_SIZE) -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rd' a = rd a) ->
  (forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
  aval_mem rd' (c + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 (Z.of_nat (length A)) ->
  sc_newargs rd' (ablocks B ly' S') c A P ->
  Forall (fun pn => iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\
                    iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE) P ->
  (forall pn, In pn O -> ~ In (fst pn) (map fst P)) ->
  rec_repA B ly' S' rd' (rec_record R fn A) (O ++ P).
Proof.
  intros ly S ly' S' rd rd' R O P c A fn (Q & HQ & HO) Hn Hc HA Hfn HB HG KB Hnc Hf Hna HP HPa HPd.
  rewrite (rec_record_calls R fn A Hn). unfold rec_repA.
  exists (RLay (l_calls Q ++ [P]) (l_spill Q) (l_answer Q) (l_reply Q)). split.
  - refine (sc3_arep_slot _ _ rd rd' R Q P c fn A HQ Hn Hc HA Hfn _ _ HG Hnc Hf Hna HP HPa _).
    + intros pn _ Hb. exact (HB pn Hb).
    + intros [p n] Hpn i Hi. exact (KB p n i (proj2 (HO (p, n)) Hpn) Hi).
    + intros pn Hpn. exact (HPd pn (proj2 (HO pn) Hpn)).
  - exact (sc3_own_iff O Q _ P HO (sc3_lay_slot_perm Q P)).
Qed.

(* the table arm in the dispatcher's form: every byte outside the slot and g_rec.ncalls kept *)
Lemma scA_record_slot : forall ly S ly' S' rd rd' R O P c A fn,
  rec_repA B ly S rd R O ->
  (length (r_calls R) < 16)%nat ->
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
  (length A <= 6)%nat -> 0 <= fn < REC_FN_COUNT ->
  (forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly' S')) ->
  (forall a, ~ (c <= a < c + CALL_SIZE) ->
             ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rd' a = rd a) ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
  aval_mem rd' (c + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 (Z.of_nat (length A)) ->
  sc_newargs rd' (ablocks B ly' S') c A P ->
  Forall (fun pn => iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\
                    iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE) P ->
  (forall pn, In pn O -> ~ In (fst pn) (map fst P)) ->
  rec_repA B ly' S' rd' (rec_record R fn A) (O ++ P).
Proof.
  intros ly S ly' S' rd rd' R O P c A fn (Q & HQ & HO) Hn Hc HA Hfn HB HG Hnc Hf Hna HP HPa HPd.
  pose proof HQ as (_ & _ & _ & _ & _ & _ & _ & _ & HW2).
  rewrite (rec_record_calls R fn A Hn). unfold rec_repA.
  exists (RLay (l_calls Q ++ [P]) (l_spill Q) (l_answer Q) (l_reply Q)). split.
  - refine (sc3_arep_slot _ _ rd rd' R Q P c fn A HQ Hn Hc HA Hfn _ _ _ Hnc Hf Hna HP HPa _).
    + intros pn _ Hb. exact (HB pn Hb).
    + intros pn Hpn i Hi. destruct (HW2 pn Hpn) as [Ha1 _]. apply HG; sc3_lia.
    + intros a _ Ha1 Ha2. exact (HG a Ha1 Ha2).
    + intros pn Hpn. exact (HPd pn (proj2 (HO pn) Hpn)).
  - exact (sc3_own_iff O Q _ P HO (sc3_lay_slot_perm Q P)).
Qed.

(* L1, as the walk uses it: record()'s table arm before any argument, nargs := 0 *)
Lemma scA_record_slot0 : forall ly S ly' S' rd rd' R O c fn,
  rec_repA B ly S rd R O ->
  (length (r_calls R) < 16)%nat ->
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
  0 <= fn < REC_FN_COUNT ->
  (forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly' S')) ->
  (forall a, ~ (c <= a < c + CALL_SIZE) ->
             ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rd' a = rd a) ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
  aval_mem rd' (c + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 0 ->
  rec_repA B ly' S' rd' (rec_record R fn []) O.
Proof.
  intros ly S ly' S' rd rd' R O c fn HR Hn Hc Hfn HB HG Hnc Hf Hn0.
  pose proof (scA_record_slot ly S ly' S' rd rd' R O [] c [] fn HR Hn Hc (Nat.le_0_l 6) Hfn HB HG Hnc Hf Hn0
    (sc_newargs_nil _ _ _) ltac:(constructor) (fun pn _ H => H)) as H.
  rewrite app_nil_r in H. exact H.
Qed.

Lemma scA_record_slot0_fr : forall ly S ly' S' rd rd' R O c fn,
  rec_repA B ly S rd R O ->
  (length (r_calls R) < 16)%nat ->
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
  0 <= fn < REC_FN_COUNT ->
  (forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly' S')) ->
  (forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
     ~ (c <= a < c + CALL_SIZE) -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rd' a = rd a) ->
  (forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
  aval_mem rd' (c + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 0 ->
  rec_repA B ly' S' rd' (rec_record R fn []) O.
Proof.
  intros ly S ly' S' rd rd' R O c fn HR Hn Hc Hfn HB HG KB Hnc Hf Hn0.
  pose proof (scA_record_slot_fr ly S ly' S' rd rd' R O [] c [] fn HR Hn Hc (Nat.le_0_l 6) Hfn HB HG KB Hnc Hf Hn0
    (sc_newargs_nil _ _ _) ltac:(constructor) (fun pn _ H => H)) as H.
  rewrite app_nil_r in H. exact H.
Qed.

(* L2: record()'s spill arm after rec_calls_free (whose post gives the recorder with the spill's arguments gone,
   rec_calls_free_c.v:106-109): the stores of fn and nargs := 0 to record.spill, framed *)
Lemma scA_spill_fn : forall ly S rd rd' R O fn0 fn,
  rec_repA B ly S rd (set_spill R (fn0, [])) O ->
  0 <= fn < REC_FN_COUNT ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
  (forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
     ~ (A_REC_SPILL + CALL_OFF_FN <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) -> rd' a = rd a) ->
  (forall q n i, In (q, n) O -> 0 <= i < n -> rd' (q + i) = rd (q + i)) ->
  rec_repA B ly S rd' (set_spill R (fn, [])) O.
Proof.
  intros ly S rd rd' R O fn0 fn (Q & HQ & HO) Hfn Hf Hn0 HG KB.
  exists Q. split; [|exact HO].
  change (set_spill R (fn, [])) with (set_spill (set_spill R (fn0, [])) (fn, [])).
  refine (sc3_arep_spill_fn _ rd rd' (set_spill R (fn0, [])) Q fn HQ eq_refl Hfn Hf Hn0 HG _).
  intros [q n] Hpn j Hj. exact (KB q n j (proj2 (HO (q, n)) Hpn) Hj).
Qed.

(* L2 with every byte outside the two words kept *)
Lemma scA_spill_fn_g : forall ly S rd rd' R O fn0 fn,
  rec_repA B ly S rd (set_spill R (fn0, [])) O ->
  0 <= fn < REC_FN_COUNT ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
  (forall a, ~ (A_REC_SPILL + CALL_OFF_FN <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) -> rd' a = rd a) ->
  rec_repA B ly S rd' (set_spill R (fn, [])) O.
Proof.
  intros ly S rd rd' R O fn0 fn HR Hfn Hf Hn0 HG.
  pose proof HR as (Q & HQ & HO). pose proof HQ as (_ & _ & _ & _ & _ & _ & _ & _ & HW2).
  apply (scA_spill_fn ly S rd rd' R O fn0 fn HR Hfn Hf Hn0).
  - intros a _ Ha. exact (HG a Ha).
  - intros q n i Hq Hi. destruct (HW2 (q, n) (proj1 (HO (q, n)) Hq)) as [_ Ha2]. cbn [fst snd] in Ha2.
    apply HG. sc3_lia.
Qed.

(* L3: one argument s appended to the call e of slot c (arg_i's or arg_s's post), framed: nargs and the new
   args[] word written, the new block (p, |s| + 1) live, every other byte of g_rec and record.spill and every byte
   of the recorder's blocks O kept *)
Lemma scA_push_arg : forall ly S ly' S' rd rd' R O k e c s p,
  rec_repA B ly S rd R O ->
  sc_target R k e c ->
  (length (snd e) < 6)%nat ->
  (forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly' S')) ->
  (forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
     ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
     ~ (c + CALL_OFF_ARGS + 8 * Z.of_nat (length (snd e)) <= a <
        c + CALL_OFF_ARGS + 8 * Z.of_nat (length (snd e)) + 8) -> rd' a = rd a) ->
  (forall q n i, In (q, n) O -> 0 <= i < n -> rd' (q + i) = rd (q + i)) ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 (Z.of_nat (length (snd e)) + 1) ->
  aval_mem rd' (c + CALL_OFF_ARGS + 8 * Z.of_nat (length (snd e))) 8 p ->
  astr_atR rd' p s -> Z.of_nat (length s) <= LMAX -> p <> 0 ->
  In (p, Z.of_nat (length s) + 1) (ablocks B ly' S') ->
  iv_apart p (Z.of_nat (length s) + 1) A_G_REC REC_SIZE ->
  iv_apart p (Z.of_nat (length s) + 1) A_REC_SPILL SC_SIZE ->
  ~ In p (map fst O) ->
  rec_repA B ly' S' rd' (sc_push_arg R k s) (O ++ [(p, Z.of_nat (length s) + 1)]).
Proof.
  intros ly S ly' S' rd rd' R O k e c s p (Q & HQ & HO) HT Hm HB HG KB Hna Hpa Hs HsL Hp0 Hin Hag Has Hfr.
  assert (TK : forall pn, In pn (lay_blocks Q) -> forall j, 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)).
  { intros [q n] Hpn j Hj. exact (KB q n j (proj2 (HO (q, n)) Hpn) Hj). }
  assert (Hfr' : ~ In p (map fst (lay_blocks Q))).
  { intro H. apply Hfr. apply in_map_iff in H as (pn & Ep & Hpn). subst p. apply in_map. exact (proj2 (HO pn) Hpn). }
  unfold rec_repA. destruct k as [i|]; destruct HT as [HT1 HT2].
  - assert (Hi : (i < length (l_calls Q))%nat).
    { pose proof HQ as (_ & _ & _ & (_ & C2 & _) & _). rewrite C2. apply nth_error_Some. rewrite HT1. discriminate. }
    exists (RLay (sc_upd i (fun P => P ++ [(p, Z.of_nat (length s) + 1)]) (l_calls Q)) (l_spill Q) (l_answer Q)
      (l_reply Q)).
    split.
    + exact (sc3_arep_push_tab _ _ rd rd' R Q i e c s p HQ HT1 HT2 Hm HB HG TK Hna Hpa Hs HsL Hp0 Hin Hag Has Hfr').
    + exact (sc3_own_iff O Q _ _ HO (sc3_lay_push_tab_perm Q i (p, Z.of_nat (length s) + 1) Hi)).
  - subst e.
    exists (RLay (l_calls Q) (l_spill Q ++ [(p, Z.of_nat (length s) + 1)]) (l_answer Q) (l_reply Q)).
    split.
    + exact (sc3_arep_push_spill _ _ rd rd' R Q c s p HQ HT2 Hm HB HG TK Hna Hpa Hs HsL Hp0 Hin Hag Has Hfr').
    + exact (sc3_own_iff O Q _ _ HO (sc3_lay_push_spill_perm Q (p, Z.of_nat (length s) + 1))).
Qed.

End e.
End d.
