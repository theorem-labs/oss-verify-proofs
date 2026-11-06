(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: block P of sup_pin_accept's ASan walk (plugin-hostd/fuzz_command): the entry,
   the inlined record(13) with both of its arms (the call of rec_calls_free on record.spill when the table already
   holds 16 calls), the two instrumented checks on the slot and the `bnez s1` join, after
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the seed of a walk segment, the run, the step through a program call)
   over fuzz_command's listing; it finishes the function by lib/A/Prog/sup_pin_accept_s2.v's `spa_from_B0`. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_pin_accept_s4.v, with its module paths and module names changed; 564 of its 678 lines of code are new or changed and 1091 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied verbatim from lib/B/Prog/sup_chain_clear_rec.v (a working branch
   b23f4439f75) for the B walk of sup_instance_verb, which appends two arguments (arg_line's canonical line, arg_s's
   ledger text) to record()'s slot: rec_repA_arg, rec_slotA_home, rec_slotA_entry. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/sup_chain_clear_s1.v (a working branch abd8a14a6b8) for fuzz_command.asan-ubsan, the representation lemmas the B walk of sup_chain_clear uses (lib/B/Prog/sup_chain_clear.v): module paths only. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/plugin-hostd/fuzz_command/lib/Prog/RecStep.v to the ASan
   representation lib/B/Prog/CmdRep.v (rec_repA / arep_at over a reader), for the walk of sup_chain_clear. *)
(* Modified by Theorem Labs, 2026-10: the keep lemmas for aval_mem, abytes_atR, astr_atR and acall_at and the
   block lemma arep_at_in follow proofs/plugin-hostd/fuzz_command/lib/A/Prog/RecBLemmas.v (aval_mem_agree_in,
   astr_atR_agree_in, acall_at_agree, acall_at_in, lay_blocks_in), restated with the keep premise in point form. *)

(* The recorder's representation on the ASan side, step by step, as the plain proof's RecStep.v states it on the
   plain side (rec_rep_record_lt :63, rep_at_record_full :395, call_at_arg :442, rep_at_arg_lt :487,
   rep_at_arg_full :582, rec_rep_arg :650, ans_entry_record :803):

   - `rec_repA_keep`: the representation reads only g_rec, record.spill and the recorder's own blocks.
   - `rec_repA_record_lt` / `rec_repA_spill_fn`: record(fn) wrote ncalls and the slot's fn and nargs (table arm),
     or fn and nargs of the emptied spill (spill arm).
   - `rec_repA_arg`: arg_i appended one argument to the slot of the current call.
   - `rec_repA_ncalls`, `rec_repA_blocks`, `rec_repA_answer`, `rec_repA_spill`: the facts a walk reads off it.
   - `rec_slotA_entry`, `rec_slotA_home`: the slot of the current call (the plain proof's rec_entry).

   The plain proof's `bytes_at .. (le4 ..)` is `aval_mem rd a 4 v` here, a kept byte is `rd' a = rd a`, a C string
   is `astr_atR`, and there is no writability conjunct (arep_at has none). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the bytes the representation reads besides the recorder's blocks: g_rec and record.spill *)
Definition in_recA (a : Z) : Prop := A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.
(* the slot record() fills: the next free table entry, or the spill when the table is full (plain rec_entry) *)
Definition rec_slotA (R : rstate) : Z :=
  if Nat.ltb (length (r_calls R)) 16 then A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) else A_REC_SPILL.
(* every block of O is still live in bl' and keeps its bytes *)
Definition rd_keepsO (rd rd' : reader) (bl' : list (Z * Z)) (O : list (Z * Z)) : Prop :=
  forall pn, In pn O -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i).

(* ---- keep lemmas over a reader ---- *)

Lemma aval_mem_keep : forall rd rd' a n v,
  aval_mem rd a n v -> (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma abytes_atR_keep : forall rd rd' a l,
  abytes_atR rd a l -> (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma astr_atR_keep : forall rd rd' p s,
  astr_atR rd p s -> (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H Hn] K. split; [|exact Hn].
  apply (abytes_atR_keep rd); [exact H|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply K. lia.
Qed.

Lemma blk_keep_at : forall (rd rd' : reader) p n x,
  (forall i, 0 <= i < n -> rd' (p + i) = rd (p + i)) -> p <= x < p + n -> rd' x = rd x.
Proof. intros rd rd' p n x K Hx. replace x with (p + (x - p)) by lia. apply K. lia. Qed.

Lemma acall_at_keep : forall bl bl' rd rd' a c P,
  acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk) K KP.
  unfold acall_at. unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  split; [exact Hfn|]. split; [exact Hn|]. split; [exact Hl|].
  split; [apply (aval_mem_keep rd); [exact Hb0 | intros x Hx; apply K; lia]|].
  split; [apply (aval_mem_keep rd); [exact Hb1 | intros x Hx; apply K; lia]|].
  split; [exact Hnd|].
  intros k s pn Es Ep. destruct (Hk k s pn Es Ep) as (Hs & Hp0 & Hin & Hsz & Hstr).
  assert (Hkl : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  destruct (KP pn (nth_error_In P k Ep)) as [Hin' Kp].
  split; [apply (aval_mem_keep rd); [exact Hs | intros x Hx; apply K; lia]|].
  split; [exact Hp0|]. split; [exact Hin'|]. split; [exact Hsz|].
  apply (astr_atR_keep rd); [exact Hstr|]. intros x Hx.
  apply (blk_keep_at rd rd' (fst pn) (snd pn)); [exact Kp | lia].
Qed.

Lemma aanswer_at_keep : forall bl bl' rd rd' gr t q,
  aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q HA K KQ. revert HA KQ. unfold aanswer_at.
  destruct t as [s|]; destruct q as [pn|]; intros HA KQ; try contradiction.
  - destruct HA as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KQ pn (or_introl eq_refl)) as [Kin Kp].
    split; [apply (aval_mem_keep rd); [exact N1 | intros y Hy; apply K; lia]|].
    split; [exact N2|]. split; [exact Kin|]. split; [exact N4|]. split; [|exact N6].
    apply (astr_atR_keep rd); [exact N5|]. intros y Hy.
    apply (blk_keep_at rd rd' (fst pn) (snd pn)); [exact Kp | lia].
  - apply (aval_mem_keep rd); [exact HA | intros y Hy; apply K; lia].
Qed.

Lemma areply_at_keep : forall bl bl' rd rd' gr t q,
  areply_at bl rd gr t q ->
  (forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY_SIZE + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  areply_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q HP K KQ. revert HP KQ. unfold areply_at. unfold OFF_REPLY, OFF_REPLY_SIZE in *.
  destruct t as [s|]; destruct q as [pn|]; intros HP KQ; try contradiction.
  - destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    destruct (KQ pn (or_introl eq_refl)) as [Kin Kp].
    split; [apply (aval_mem_keep rd); [exact P1 | intros y Hy; apply K; lia]|].
    split; [apply (aval_mem_keep rd); [exact P2 | intros y Hy; apply K; lia]|].
    split; [exact P3|]. split; [exact P4|]. split; [exact Kin|]. split; [exact P6|]. split; [|exact P8].
    apply (abytes_atR_keep rd); [exact P7|]. intros y Hy.
    apply (blk_keep_at rd rd' (fst pn) (snd pn)); [exact Kp | lia].
  - destruct HP as [P1 P2].
    split; [apply (aval_mem_keep rd); [exact P1 | intros y Hy; apply K; lia]|].
    apply (aval_mem_keep rd); [exact P2 | intros y Hy; apply K; lia].
Qed.

Lemma ag1_scalars_keep : forall rd rd' gr R,
  ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R HX K. unfold ag1_scalars in *. unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  destruct HX as (X1 & X2 & X3 & X4 & X5 & X6).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  - apply (aval_mem_keep rd); [exact X1 | intros x Hx; apply K; lia].
  - apply (aval_mem_keep rd); [exact X2 | intros x Hx; apply K; lia].
  - apply (aval_mem_keep rd); [exact X3 | intros x Hx; apply K; lia].
  - apply (aval_mem_keep rd); [exact X4 | intros x Hx; apply K; lia].
  - apply (aval_mem_keep rd); [exact X5 | intros x Hx; apply K; lia].
Qed.

(* ---- the blocks the representation names ---- *)

Lemma acall_at_in : forall bl rd a c P pn, acall_at bl rd a c P -> In pn P -> In pn bl /\ fst pn <> 0.
Proof.
  intros bl rd a c P pn (_ & _ & Hl & _ & _ & _ & Hk) Hin.
  destruct (In_nth_error P pn Hin) as [k Ek].
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (Hk k s pn Es Ek) as (_ & H0 & H1 & _). split; assumption.
Qed.

Lemma arep_at_in : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> In pn bl /\ fst pn <> 0.
Proof.
  intros bl rd gr sc R Q pn (_ & _ & _ & HC & HA & HP & _ & _) Hin.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP0 & Hpn).
    destruct (In_nth_error _ _ HP0) as [i Ei].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    exact (acall_at_in _ _ _ _ _ _ (proj1 (C4 i c P Ec Ei)) Hpn).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (acall_at_in _ _ _ _ _ _ C5 Hin)|].
    apply in_app_or in Hin as [Hin|Hin].
    + revert HA Hin. unfold aanswer_at.
      destruct (r_answer R); destruct (l_answer Q) as [pn'|]; intros HA Hin; cbn [oblk In] in Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HA as (_ & H0 & H1 & _). split; assumption.
    + revert HP Hin. unfold areply_at.
      destruct (r_reply R); destruct (l_reply Q) as [pn'|]; intros HP Hin; cbn [oblk In] in Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HP as (_ & _ & H0 & _ & H1 & _). split; assumption.
Qed.

(* ---- block-list permutations (plain RecStep.v:293-386) ---- *)

Lemma nodupA_fst_snoc : forall (l : list (Z * Z)) p k, NoDup (map fst l) -> ~ In p (map fst l) ->
  NoDup (map fst (l ++ [(p, k)])).
Proof.
  intros l p k H N. apply NoDup_ListNoDup. apply NoDup_ListNoDup in H.
  rewrite map_app. cbn [map fst]. apply (Permutation_NoDup (Permutation_cons_append _ _)).
  constructor; assumption.
Qed.

Lemma nodupA_fst_perm : forall l l' : list (Z * Z), Permutation l l' -> NoDup (map fst l) -> NoDup (map fst l').
Proof.
  intros l l' HP H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
  exact (Permutation_NoDup (Permutation_map fst HP) H).
Qed.

Lemma permA_snoc_mid : forall (X Y W : list (Z * Z)) a, Permutation (X ++ (Y ++ [a]) ++ W) ((X ++ Y ++ W) ++ [a]).
Proof.
  intros X Y W a. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
  cbn [app]. apply Permutation_cons_append.
Qed.

Lemma layA_perm_lt : forall l0 P Sp ans rep pk,
  Permutation (lay_blocks (RLay (l0 ++ [P ++ [pk]]) Sp ans rep)) (lay_blocks (RLay (l0 ++ [P]) Sp ans rep) ++ [pk]).
Proof.
  intros l0 P Sp ans rep pk.
  assert (E1 : lay_blocks (RLay (l0 ++ [P ++ [pk]]) Sp ans rep) = concat l0 ++ (P ++ [pk]) ++ Sp ++ oblk ans ++ oblk rep).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
    rewrite app_nil_r. rewrite <- !app_assoc. reflexivity. }
  assert (E2 : lay_blocks (RLay (l0 ++ [P]) Sp ans rep) = concat l0 ++ P ++ Sp ++ oblk ans ++ oblk rep).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
    rewrite app_nil_r. rewrite <- !app_assoc. reflexivity. }
  rewrite E1, E2. apply permA_snoc_mid.
Qed.

Lemma layA_perm_full : forall lc Sp ans rep pk,
  Permutation (lay_blocks (RLay lc (Sp ++ [pk]) ans rep)) (lay_blocks (RLay lc Sp ans rep) ++ [pk]).
Proof. intros lc Sp ans rep pk. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply permA_snoc_mid. Qed.

Lemma layA_perm_iff : forall (O l l' : list (Z * Z)) (pk : Z * Z), (forall pn, In pn O <-> In pn l) ->
  Permutation l' (l ++ [pk]) ->
  forall pn, In pn (O ++ [pk]) <-> In pn l'.
Proof.
  intros O l l' pk HO HP pn. split; intros H.
  - apply (Permutation_in _ (Permutation_sym HP)). apply in_app_or in H as [H|H]; apply in_or_app;
      [left; apply HO; exact H | right; exact H].
  - apply (Permutation_in _ HP) in H. apply in_app_or in H as [H|H]; apply in_or_app;
      [left; apply HO; exact H | right; exact H].
Qed.

(* ---- the representation, rebuilt around a new call table ---- *)

(* everything but the call table and the spill is kept: answer, reply, the scalars *)
Lemma arep_at_rest : forall bl bl' rd rd' R R' Q Q',
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  r_answer R' = r_answer R -> r_reply R' = r_reply R -> r_refuse R' = r_refuse R -> r_code R' = r_code R ->
  r_nreplies R' = r_nreplies R -> r_state R' = r_state R -> r_host R' = r_host R ->
  l_answer Q' = l_answer Q -> l_reply Q' = l_reply Q ->
  (forall a, A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + 912 <= a < A_G_REC + 960 -> rd' a = rd a) ->
  (forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl' /\
     forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  ag1_calls bl' rd' A_G_REC A_REC_SPILL R' Q' ->
  ag1_own A_G_REC A_REC_SPILL Q' ->
  arep_at bl' rd' A_G_REC A_REC_SPILL R' Q'.
Proof.
  intros bl bl' rd rd' R R' Q Q' (H1 & H2 & H3 & HC & HA & HP & HX & HW) E1 E2 E3 E4 E5 E6 E7 F1 F2 K KO HC' HW'.
  assert (HX' : ag1_scalars rd A_G_REC R') by (unfold ag1_scalars in *; rewrite E3, E4, E5, E6, E7; exact HX).
  unfold arep_at. rewrite E1, E2, F1, F2.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact HC'|].
  split.
  { apply (aanswer_at_keep bl bl' rd rd' A_G_REC _ _ HA).
    - intros x Hx. apply K. unfold OFF_ANSWER in Hx. lia.
    - intros pn Hpn. apply KO. apply in_or_app. left. exact Hpn. }
  split.
  { apply (areply_at_keep bl bl' rd rd' A_G_REC _ _ HP).
    - intros x Hx. apply K. unfold OFF_REPLY, OFF_REPLY_SIZE in Hx. lia.
    - intros pn Hpn. apply KO. apply in_or_app. right. exact Hpn. }
  split; [|exact HW'].
  apply (ag1_scalars_keep rd rd' A_G_REC R' HX'). intros x Hx. apply K. lia.
Qed.

Lemma arep_at_keep : forall bl bl' rd rd' R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (forall a, in_recA a -> rd' a = rd a) ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
  intros bl bl' rd rd' R Q HR K KQ.
  pose proof HR as (_ & _ & _ & HC & _ & _ & _ & HW).
  apply (arep_at_rest bl bl' rd rd' R R Q Q HR); try reflexivity.
  - intros a Ha. apply K. unfold in_recA, REC_SIZE. lia.
  - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn.
  - destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (aval_mem_keep rd); [exact C3 | intros x Hx; apply K; unfold in_recA, OFF_NCALLS, REC_SIZE in *; lia].
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (acall_at_keep bl bl' rd rd' _ c P Hc).
      * intros x Hx. apply K. unfold in_recA, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + apply (acall_at_keep bl bl' rd rd' _ _ _ C5).
      * intros x Hx. apply K. unfold in_recA, CALL_SIZE, SC_SIZE in *. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - exact HW.
Qed.

(* a call record with function fn and no argument yet *)
Lemma acall_at_new : forall bl rd a fn,
  0 <= fn < REC_FN_COUNT -> aval_mem rd (a + CALL_OFF_FN) 4 fn -> aval_mem rd (a + CALL_OFF_NARGS) 4 0 ->
  acall_at bl rd a (fn, []) [].
Proof.
  intros bl rd a fn Hfn BF BA. unfold acall_at. cbn [fst snd length].
  split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
  split; [exact BF|]. split; [exact BA|]. split; [cbn [map]; constructor|].
  intros k s pn Es. destruct k; discriminate.
Qed.

(* plain call_at_arg: one argument appended to a call record *)
Lemma acall_at_arg : forall bl bl' rd rd' e fn As P x p k,
  acall_at bl rd e (fn, As) P -> (length As < 6)%nat ->
  aval_mem rd' (e + CALL_OFF_NARGS) 4 (Z.of_nat (length As) + 1) ->
  aval_mem rd' (e + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) 8 p ->
  (forall a, e <= a < e + CALL_SIZE -> ~ (e + CALL_OFF_NARGS <= a < e + CALL_OFF_NARGS + 4) ->
     ~ (e + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a < e + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
     rd' a = rd a) ->
  (forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  ~ In p (map fst P) -> p <> 0 -> In (p, k) bl' -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
  astr_atR rd' p x ->
  acall_at bl' rd' e (fn, As ++ [x]) (P ++ [(p, k)]).
Proof.
  intros bl bl' rd rd' e fn As P x p k (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk) H6 BN BS K KP Hfr Hp0 Hin Hsz Hx.
  cbn [fst snd] in *.
  unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  unfold acall_at. cbn [fst snd]. unfold CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS.
  split; [exact Hfn|]. split; [rewrite length_app; cbn [length]; lia|].
  split; [rewrite !length_app, Hl; reflexivity|].
  split; [apply (aval_mem_keep rd); [exact Hb0 | intros a Ha; apply K; lia]|].
  split; [rewrite length_app, Nat2Z.inj_add; exact BN|].
  split; [exact (nodupA_fst_snoc P p k Hnd Hfr)|].
  intros j s pn Es Ep.
  destruct (Nat.lt_ge_cases j (length As)) as [Hj|Hj].
  - rewrite nth_error_app1 in Es by exact Hj. rewrite nth_error_app1 in Ep by (rewrite Hl; exact Hj).
    destruct (Hk j s pn Es Ep) as (Hs & Hq0 & Hq & Hqs & Hstr).
    destruct (KP pn (nth_error_In P j Ep)) as [Kin Kp].
    split; [apply (aval_mem_keep rd); [exact Hs | intros a Ha; apply K; lia]|].
    split; [exact Hq0|]. split; [exact Kin|]. split; [exact Hqs|].
    apply (astr_atR_keep rd); [exact Hstr|]. intros a Ha.
    apply (blk_keep_at rd rd' (fst pn) (snd pn)); [exact Kp | lia].
  - destruct (Nat.eq_dec j (length As)) as [->|Hne].
    + rewrite nth_error_app2, Nat.sub_diag in Es by lia. cbn in Es. injection Es as <-.
      rewrite nth_error_app2 in Ep by (rewrite Hl; lia). rewrite Hl, Nat.sub_diag in Ep. cbn in Ep.
      injection Ep as <-.
      cbn [fst snd]. split; [exact BS|]. split; [exact Hp0|]. split; [exact Hin|]. split; [exact Hsz | exact Hx].
    + exfalso. assert (N : nth_error (As ++ [x]) j = None)
        by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
      rewrite N in Es. discriminate.
Qed.

(* plain rep_at_arg_lt: arg append to the last table entry; e is its address *)
Lemma arep_at_arg_lt : forall bl bl' rd rd' R fn As l0 P Sp ans rep x p k e,
  arep_at bl rd A_G_REC A_REC_SPILL (set_calls R (r_calls R ++ [(fn, As)])) (RLay (l0 ++ [P]) Sp ans rep) ->
  e = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
  (length As < 6)%nat ->
  aval_mem rd' (e + CALL_OFF_NARGS) 4 (Z.of_nat (length As) + 1) ->
  aval_mem rd' (e + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) 8 p ->
  (forall a, in_recA a -> ~ (e + CALL_OFF_NARGS <= a < e + CALL_OFF_NARGS + 4) ->
     ~ (e + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a < e + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
     rd' a = rd a) ->
  (forall pn, In pn (lay_blocks (RLay (l0 ++ [P]) Sp ans rep)) -> In pn bl' /\
     forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  ~ In p (map fst (lay_blocks (RLay (l0 ++ [P]) Sp ans rep))) -> p <> 0 -> In (p, k) bl' ->
  Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 -> astr_atR rd' p x ->
  iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
  arep_at bl' rd' A_G_REC A_REC_SPILL (set_calls R (r_calls R ++ [(fn, As ++ [x])]))
    (RLay (l0 ++ [P ++ [(p, k)]]) Sp ans rep).
Proof.
  intros bl bl' rd rd' R fn As l0 P Sp ans rep x p k e HR Ee H6 BN BS KG KB Hfr Hp0 Hin Hlx Hsz Hx Ha1 Ha2.
  pose proof HR as (_ & _ & H3 & HC & _ & _ & _ & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  destruct HW as [HND HAP].
  cbn [set_calls r_calls r_spill l_calls l_spill l_answer l_reply] in C1, C2, C3, C4, C5, C6.
  assert (MB : forall pn, In pn P -> In pn (lay_blocks (RLay (l0 ++ [P]) Sp ans rep))).
  { intros pn Hpn. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply in_or_app. left.
    rewrite concat_app. apply in_or_app. right. cbn [concat]. rewrite app_nil_r. exact Hpn. }
  assert (KP : forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
    by (intros pn Hpn; apply KB; apply MB; exact Hpn).
  assert (HfrP : ~ In p (map fst P)).
  { intros Hq. apply Hfr. apply in_map_iff in Hq as (pn & E & Hq). apply in_map_iff. exists pn.
    split; [exact E | apply MB; exact Hq]. }
  assert (Hn : (length (r_calls R) < 16)%nat) by (rewrite length_app in C1; cbn [length] in C1; lia).
  assert (EL : length (r_calls R ++ [(fn, As ++ [x])]) = length (r_calls R ++ [(fn, As)]))
    by (rewrite !length_app; reflexivity).
  assert (L0 : length l0 = length (r_calls R)) by (rewrite !length_app in C2; cbn [length] in C2; lia).
  assert (Eec : nth_error (r_calls R ++ [(fn, As)]) (length (r_calls R)) = Some (fn, As))
    by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
  assert (Eep : nth_error (l0 ++ [P]) (length (r_calls R)) = Some P)
    by (rewrite nth_error_app2, L0, Nat.sub_diag by lia; reflexivity).
  destruct (C4 _ _ _ Eec Eep) as [CE CL].
  unfold iv_apart, REC_SIZE, SC_SIZE in H3.
  subst e.
  apply (arep_at_rest bl bl' rd rd' _ _ _ _ HR); try reflexivity.
  - intros a Ha. apply KG; unfold in_recA, REC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
  - intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    apply in_or_app. right. apply in_or_app. right. exact Hpn.
  - unfold ag1_calls. cbn [set_calls r_calls r_spill l_calls l_spill].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ C6))))).
    + rewrite EL. exact C1.
    + rewrite EL, <- C2, !length_app. reflexivity.
    + rewrite EL. apply (aval_mem_keep rd); [exact C3|]. intros a Ha.
      apply KG; unfold in_recA, REC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
    + intros i c P' Ec EP'.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      * assert (Ec0 : nth_error (r_calls R ++ [(fn, As)]) i = Some c).
        { rewrite nth_error_app1 in Ec by exact Hi. rewrite nth_error_app1 by exact Hi. exact Ec. }
        assert (EP0 : nth_error (l0 ++ [P]) i = Some P').
        { rewrite nth_error_app1 in EP' by lia. rewrite nth_error_app1 by lia. exact EP'. }
        destruct (C4 i c P' Ec0 EP0) as [Hc HL]. split; [|exact HL].
        apply (acall_at_keep bl bl' rd rd' _ c P' Hc).
        -- intros a Ha.
           apply KG; unfold in_recA, REC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
        -- intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
           apply in_or_app. left. apply in_concat. exists P'. split; [eapply nth_error_In; exact EP0 | exact Hpn].
      * destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
        -- rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
           rewrite nth_error_app2, L0, Nat.sub_diag in EP' by lia. cbn in EP'. injection EP' as <-.
           split; [|apply Forall_app; split; [exact CL | constructor; [exact Hlx | constructor]]].
           apply (acall_at_arg bl bl' rd rd' _ fn As P x p k CE H6 BN BS);
             [| exact KP | exact HfrP | exact Hp0 | exact Hin | exact Hsz | exact Hx].
           intros a Ha N1 N2. apply KG; [unfold in_recA, REC_SIZE, OFF_CALLS, CALL_SIZE in *; lia | exact N1 | exact N2].
        -- exfalso. assert (N : nth_error (r_calls R ++ [(fn, As ++ [x])]) i = None)
             by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
           rewrite N in Ec. discriminate.
    + apply (acall_at_keep bl bl' rd rd' _ _ _ C5).
      * intros a Ha.
        apply KG; unfold in_recA, REC_SIZE, SC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
      * intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
        apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - unfold ag1_own. pose proof (layA_perm_lt l0 P Sp ans rep (p, k)) as PERM. split.
    + apply (nodupA_fst_perm _ _ (Permutation_sym PERM)). apply nodupA_fst_snoc; [exact HND | exact Hfr].
    + intros pn Hpn. apply (Permutation_in _ PERM) in Hpn. apply in_app_or in Hpn as [Hpn|[<-|[]]];
        [exact (HAP pn Hpn)|]. cbn [fst snd]. split; assumption.
Qed.

(* plain rep_at_arg_full: arg append to the spill *)
Lemma arep_at_arg_full : forall bl bl' rd rd' R fn As lc Sp ans rep x p k,
  arep_at bl rd A_G_REC A_REC_SPILL (set_spill R (fn, As)) (RLay lc Sp ans rep) ->
  (length As < 6)%nat ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 (Z.of_nat (length As) + 1) ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) 8 p ->
  (forall a, in_recA a -> ~ (A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) ->
     ~ (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
        A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
     rd' a = rd a) ->
  (forall pn, In pn (lay_blocks (RLay lc Sp ans rep)) -> In pn bl' /\
     forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  ~ In p (map fst (lay_blocks (RLay lc Sp ans rep))) -> p <> 0 -> In (p, k) bl' ->
  Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 -> astr_atR rd' p x ->
  iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
  arep_at bl' rd' A_G_REC A_REC_SPILL (set_spill R (fn, As ++ [x])) (RLay lc (Sp ++ [(p, k)]) ans rep).
Proof.
  intros bl bl' rd rd' R fn As lc Sp ans rep x p k HR H6 BN BS KG KB Hfr Hp0 Hin Hlx Hsz Hx Ha1 Ha2.
  pose proof HR as (_ & _ & H3 & HC & _ & _ & _ & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  destruct HW as [HND HAP].
  cbn [set_spill r_calls r_spill l_calls l_spill fst snd] in C1, C2, C3, C4, C5, C6.
  assert (MB : forall pn, In pn Sp -> In pn (lay_blocks (RLay lc Sp ans rep))).
  { intros pn Hpn. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply in_or_app. right.
    apply in_or_app. left. exact Hpn. }
  assert (KP : forall pn, In pn Sp -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
    by (intros pn Hpn; apply KB; apply MB; exact Hpn).
  assert (HfrP : ~ In p (map fst Sp)).
  { intros Hq. apply Hfr. apply in_map_iff in Hq as (pn & E & Hq). apply in_map_iff. exists pn.
    split; [exact E | apply MB; exact Hq]. }
  unfold iv_apart, REC_SIZE, SC_SIZE in H3.
  apply (arep_at_rest bl bl' rd rd' _ _ _ _ HR); try reflexivity.
  - intros a Ha. apply KG; unfold in_recA, REC_SIZE, SC_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
  - intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    apply in_or_app. right. apply in_or_app. right. exact Hpn.
  - unfold ag1_calls. cbn [set_spill r_calls r_spill l_calls l_spill fst snd].
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ _))))).
    + apply (aval_mem_keep rd); [exact C3|]. intros a Ha.
      apply KG; unfold in_recA, REC_SIZE, SC_SIZE, OFF_NCALLS, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
    + intros i c P' Ec EP'. destruct (C4 i c P' Ec EP') as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (acall_at_keep bl bl' rd rd' _ c P' Hc).
      * intros a Ha.
        apply KG; unfold in_recA, REC_SIZE, SC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
      * intros pn Hpn. apply KB. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
        apply in_or_app. left. apply in_concat. exists P'. split; [eapply nth_error_In; exact EP' | exact Hpn].
    + apply (acall_at_arg bl bl' rd rd' A_REC_SPILL fn As Sp x p k C5 H6 BN BS);
        [| exact KP | exact HfrP | exact Hp0 | exact Hin | exact Hsz | exact Hx].
      intros a Ha N1 N2. apply KG; [unfold in_recA, CALL_SIZE, SC_SIZE in *; lia | exact N1 | exact N2].
    + apply Forall_app. split; [exact C6 | constructor; [exact Hlx | constructor]].
  - unfold ag1_own. pose proof (layA_perm_full lc Sp ans rep (p, k)) as PERM. split.
    + apply (nodupA_fst_perm _ _ (Permutation_sym PERM)). apply nodupA_fst_snoc; [exact HND | exact Hfr].
    + intros pn Hpn. apply (Permutation_in _ PERM) in Hpn. apply in_app_or in Hpn as [Hpn|[<-|[]]];
        [exact (HAP pn Hpn)|]. cbn [fst snd]. split; assumption.
Qed.

Section d. Variable B : asyms.
(* the representation survives any change outside g_rec, record.spill and the recorder's blocks *)
Lemma rec_repA_keep : forall ly S rd ly' S' rd' R O,
  rec_repA B ly S rd R O -> (forall a, in_recA a -> rd' a = rd a) -> rd_keepsO rd rd' (ablocks B ly' S') O ->
  rec_repA B ly' S' rd' R O.
Proof.
  intros ly S rd ly' S' rd' R O (Q & HR & HO) K KO. unfold rd_keepsO in KO.
  exists Q. split; [|exact HO].
  apply (arep_at_keep _ _ rd rd' R Q HR K). intros pn Hpn. apply KO. apply HO. exact Hpn.
Qed.

(* record(fn), slot arm (plain rec_rep_record_lt) *)
Lemma rec_repA_record_lt : forall ly S rd ly' S' rd' R O fn,
  rec_repA B ly S rd R O -> (length (r_calls R) < 16)%nat -> 0 <= fn < REC_FN_COUNT ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
  aval_mem rd' (rec_slotA R + CALL_OFF_FN) 4 fn -> aval_mem rd' (rec_slotA R + CALL_OFF_NARGS) 4 0 ->
  (forall a, in_recA a -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
     ~ (rec_slotA R <= a < rec_slotA R + 8) -> rd' a = rd a) ->
  rd_keepsO rd rd' (ablocks B ly' S') O ->
  rec_repA B ly' S' rd' (rec_record R fn []) O.
Proof.
  intros ly S rd ly' S' rd' R O fn (Q & HR & HO) Hn Hfn BN BF BA KG KO.
  unfold rd_keepsO in KO.
  assert (ES : rec_slotA R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))
    by (unfold rec_slotA; apply Nat.ltb_lt in Hn; rewrite Hn; reflexivity).
  rewrite ES in BF, BA, KG.
  rewrite (rec_record_calls R fn [] Hn).
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S') /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
    by (intros pn Hpn; apply KO; apply HO; exact Hpn).
  assert (LB : lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
    rewrite !app_nil_r. reflexivity. }
  exists (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)). split; [|rewrite LB; exact HO].
  pose proof HR as (_ & _ & H3 & HC & _ & _ & _ & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold iv_apart, REC_SIZE, SC_SIZE in H3.
  apply (arep_at_rest _ _ rd rd' R _ Q _ HR); try reflexivity.
  - intros a Ha. apply KG; unfold in_recA, REC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
  - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn.
  - unfold ag1_calls. cbn [set_calls r_calls r_spill l_calls l_spill].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ C6))))).
    + rewrite length_app. cbn [length]. lia.
    + rewrite !length_app, C2. reflexivity.
    + rewrite length_app, Nat2Z.inj_add. exact BN.
    + intros i c P Ec EP.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      * rewrite nth_error_app1 in Ec by exact Hi. rewrite nth_error_app1 in EP by (rewrite C2; exact Hi).
        destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
        apply (acall_at_keep _ _ rd rd' _ c P Hc).
        -- intros x Hx. apply KG; unfold in_recA, REC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
        -- intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
           exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
      * destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
        -- rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
           rewrite nth_error_app2 in EP by (rewrite C2; lia). rewrite C2, Nat.sub_diag in EP. cbn in EP.
           injection EP as <-.
           split; [exact (acall_at_new _ rd' _ fn Hfn BF BA) | constructor].
        -- exfalso. assert (N : nth_error (r_calls R ++ [(fn, [])]) i = None)
             by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
           rewrite N in Ec. discriminate.
    + apply (acall_at_keep _ _ rd rd' _ _ _ C5).
      * intros x Hx. apply KG; unfold in_recA, REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - unfold ag1_own. rewrite LB. exact HW.
Qed.

(* record(fn), spill arm, after rec_calls_free emptied the spill (fn and nargs written) *)
Lemma rec_repA_spill_fn : forall ly S rd ly' S' rd' R O fn,
  rec_repA B ly S rd R O -> snd (r_spill R) = [] -> 0 <= fn < REC_FN_COUNT ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 fn -> aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
  (forall a, in_recA a -> ~ (A_REC_SPILL <= a < A_REC_SPILL + 8) -> rd' a = rd a) ->
  rd_keepsO rd rd' (ablocks B ly' S') O ->
  rec_repA B ly' S' rd' (set_spill R (fn, [])) O.
Proof.
  intros ly S rd ly' S' rd' R O fn (Q & HR & HO) Hs0 Hfn BF BA KG KO.
  unfold rd_keepsO in KO.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S') /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
    by (intros pn Hpn; apply KO; apply HO; exact Hpn).
  exists Q. split; [|exact HO].
  pose proof HR as (_ & _ & H3 & HC & _ & _ & _ & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold iv_apart, REC_SIZE, SC_SIZE in H3.
  assert (Els : l_spill Q = []).
  { destruct C5 as (_ & _ & Hl & _). rewrite Hs0 in Hl. apply length_zero_iff_nil. exact Hl. }
  apply (arep_at_rest _ _ rd rd' R _ Q Q HR); try reflexivity.
  - intros a Ha. apply KG; unfold in_recA, REC_SIZE, SC_SIZE in *; lia.
  - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn.
  - unfold ag1_calls. cbn [set_spill r_calls r_spill fst snd].
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ (Forall_nil _)))))).
    + apply (aval_mem_keep rd); [exact C3|]. intros x Hx.
      apply KG; unfold in_recA, REC_SIZE, SC_SIZE, OFF_NCALLS in *; lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (acall_at_keep _ _ rd rd' _ c P Hc).
      * intros x Hx. apply KG; unfold in_recA, REC_SIZE, SC_SIZE, OFF_CALLS, CALL_SIZE in *; lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + rewrite Els. exact (acall_at_new _ rd' _ fn Hfn BF BA).
  - exact HW.
Qed.

(* arg append (plain rec_rep_arg) *)
Lemma rec_repA_arg : forall ly S rd ly' S' rd' R fn As O x p k,
  rec_repA B ly S rd (rec_record R fn As) O -> (length As < 6)%nat ->
  aval_mem rd' (rec_slotA R + CALL_OFF_NARGS) 4 (Z.of_nat (length As) + 1) ->
  aval_mem rd' (rec_slotA R + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) 8 p ->
  (forall a, in_recA a -> ~ (rec_slotA R + CALL_OFF_NARGS <= a < rec_slotA R + CALL_OFF_NARGS + 4) ->
     ~ (rec_slotA R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a < rec_slotA R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
     rd' a = rd a) ->
  rd_keepsO rd rd' (ablocks B ly' S') O ->
  ~ In p (map fst O) -> p <> 0 -> In (p, k) (ablocks B ly' S') ->
  Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 -> astr_atR rd' p x ->
  iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
  rec_repA B ly' S' rd' (rec_record R fn (As ++ [x])) (O ++ [(p, k)]).
Proof.
  intros ly S rd ly' S' rd' R fn As O x p k (Q & HR & HO) H6 BN BS KG KO Hfr Hp0 Hin Hlx Hsz Hx Ha1 Ha2.
  unfold rd_keepsO in KO.
  assert (KB : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S') /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
    by (intros pn Hpn; apply KO; apply HO; exact Hpn).
  assert (Hfr' : ~ In p (map fst (lay_blocks Q))).
  { intros Hq. apply Hfr. apply in_map_iff in Hq as (pn & E & Hq). apply in_map_iff. exists pn.
    split; [exact E | apply HO; exact Hq]. }
  destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hn|Hn].
  - assert (ES : rec_slotA R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))
      by (unfold rec_slotA; apply Nat.ltb_lt in Hn; rewrite Hn; reflexivity).
    rewrite (rec_record_calls R fn As Hn) in HR. rewrite (rec_record_calls R fn (As ++ [x]) Hn).
    destruct Q as [lc ls la lr].
    pose proof HR as (_ & _ & _ & (_ & C2 & _) & _).
    cbn [set_calls r_calls l_calls] in C2. rewrite length_app in C2. cbn [length] in C2.
    assert (NE : lc <> []) by (intros E; rewrite E in C2; cbn in C2; lia).
    destruct (exists_last NE) as (l0 & P & E). subst lc.
    exists (RLay (l0 ++ [P ++ [(p, k)]]) ls la lr). split.
    + exact (arep_at_arg_lt _ _ rd rd' R fn As l0 P ls la lr x p k (rec_slotA R)
               HR ES H6 BN BS KG KB Hfr' Hp0 Hin Hlx Hsz Hx Ha1 Ha2).
    + exact (layA_perm_iff O _ _ (p, k) HO (layA_perm_lt l0 P ls la lr (p, k))).
  - assert (ER : forall Bs, rec_record R fn Bs = set_spill R (fn, Bs)).
    { intros Bs. unfold rec_record. destruct (Nat.ltb_spec (length (r_calls R)) 16); [lia | reflexivity]. }
    assert (ES : rec_slotA R = A_REC_SPILL).
    { unfold rec_slotA. destruct (Nat.ltb_spec (length (r_calls R)) 16); [lia | reflexivity]. }
    rewrite ES in BN, BS, KG.
    rewrite ER in HR. rewrite ER.
    destruct Q as [lc ls la lr].
    exists (RLay lc (ls ++ [(p, k)]) la lr). split.
    + exact (arep_at_arg_full _ _ rd rd' R fn As lc ls la lr x p k HR H6 BN BS KG KB Hfr' Hp0 Hin Hlx Hsz Hx Ha1 Ha2).
    + exact (layA_perm_iff O _ _ (p, k) HO (layA_perm_full lc ls la lr (p, k))).
Qed.

(* the facts a walk reads off the representation *)
Lemma rec_repA_ncalls : forall ly S rd R O, rec_repA B ly S rd R O ->
  (length (r_calls R) <= 16)%nat /\ aval_mem rd (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R))).
Proof. intros ly S rd R O (Q & (_ & _ & _ & (C1 & _ & C3 & _) & _) & _). split; assumption. Qed.

Lemma rec_repA_blocks : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O ->
  In pn (ablocks B ly S) /\ fst pn <> 0 /\ iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE.
Proof.
  intros ly S rd R O (Q & HR & HO) pn Hpn. apply HO in Hpn.
  destruct (arep_at_in _ _ _ _ _ _ pn HR Hpn) as [H1 H2].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & (_ & HAP)).
  destruct (HAP pn Hpn) as [H3 H4]. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma rec_repA_answer : forall ly S rd R O, rec_repA B ly S rd R O ->
  exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists pn, In pn O /\ fst pn = old).
Proof.
  intros ly S rd R O (Q & HR & HO).
  pose proof HR as (_ & _ & _ & _ & HA & _).
  revert HA. unfold aanswer_at.
  destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn|] eqn:EA; intros HA; try contradiction.
  - destruct HA as (N1 & _). exists (fst pn). split; [exact N1|]. right. exists pn. split; [|reflexivity].
    apply HO. unfold lay_blocks. rewrite EA. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    left. reflexivity.
  - exists 0. split; [exact HA | left; reflexivity].
Qed.

(* the spill entry, in the form rec_calls_free's pre asks it (rec_calls_free_c.v:80-87, i = 0, c = A_REC_SPILL) *)
Lemma rec_repA_spill : forall ly S rd R O, rec_repA B ly S rd R O -> exists Q,
  arep_at (ablocks B ly S) rd A_G_REC A_REC_SPILL R Q /\ (forall pn, In pn O <-> In pn (lay_blocks Q)) /\
  (length (l_spill Q) <= 6)%nat /\ length (l_spill Q) = length (snd (r_spill R)) /\
  aval_mem rd (A_REC_SPILL + CALL_OFF_NARGS) 4 (Z.of_nat (length (l_spill Q))) /\
  (forall a pn, nth_error (l_spill Q) a = Some pn ->
     aval_mem rd (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\ In pn (ablocks B ly S)) /\
  NoDup (map fst (l_spill Q)) /\
  (forall pn, In pn (lay_blocks Q) <-> In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) \/ In pn (l_spill Q)).
Proof.
  intros ly S rd R O (Q & HR & HO). exists Q.
  pose proof HR as (_ & _ & _ & (_ & _ & _ & _ & C5 & _) & _).
  destruct C5 as (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk).
  split; [exact HR|]. split; [exact HO|].
  split; [rewrite Hl; exact Hn|]. split; [exact Hl|].
  split; [rewrite Hl; exact Hb1|].
  split.
  - intros a pn Ea.
    assert (Hal : (a < length (snd (r_spill R)))%nat)
      by (rewrite <- Hl; apply nth_error_Some; rewrite Ea; discriminate).
    destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
    destruct (Hk a s pn Es Ea) as (V & _ & Hin & _). split; [exact V | exact Hin].
  - split; [exact Hnd|].
    intros pn. unfold lay_blocks. split.
    + intros H. apply in_app_or in H as [H|H]; [left; apply in_or_app; left; exact H|].
      apply in_app_or in H as [H|H]; [right; exact H|]. left. apply in_or_app. right. exact H.
    + intros [H|H].
      * apply in_app_or in H as [H|H]; [apply in_or_app; left; exact H|].
        apply in_or_app. right. apply in_or_app. right. exact H.
      * apply in_or_app. right. apply in_or_app. left. exact H.
Qed.
End d.

(* answer's entry premise (answer_c.v:103-105), plain ans_entry_record *)
Lemma rec_slotA_entry : forall R fn As, (length (r_calls R) <= 16)%nat ->
  (exists k, nth_error (r_calls (rec_record R fn As)) k = Some (fn, As) /\
     rec_slotA R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
  (rec_slotA R = A_REC_SPILL /\ (fn, As) = r_spill (rec_record R fn As)).
Proof.
  intros R fn As H.
  destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hl|Hg].
  - left. exists (length (r_calls R)). rewrite (rec_record_calls R fn As Hl).
    unfold rec_slotA. apply Nat.ltb_lt in Hl. rewrite Hl. cbn [set_calls r_calls].
    split; [rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | reflexivity].
  - right. assert (E : length (r_calls R) = 16%nat) by lia.
    rewrite (rec_record_spill R fn As E). unfold rec_slotA. rewrite E. split; reflexivity.
Qed.

(* arg_i's slot premise (arg_i_c.v:82) and the slot's bounds *)
Lemma rec_slotA_home : forall R, (length (r_calls R) <= 16)%nat ->
  ((exists i, 0 <= i < REC_CALLS_MAX /\ rec_slotA R = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ rec_slotA R = A_REC_SPILL) /\
  A_G_REC + OFF_CALLS <= rec_slotA R /\ rec_slotA R + CALL_SIZE <= A_REC_SPILL + SC_SIZE /\ rec_slotA R mod 8 = 0 /\
  (rec_slotA R + CALL_SIZE <= A_G_REC + REC_SIZE \/ rec_slotA R = A_REC_SPILL).
Proof.
  intros R H.
  destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hl|Hg].
  - assert (ES : rec_slotA R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)))
      by (unfold rec_slotA; apply Nat.ltb_lt in Hl; rewrite Hl; reflexivity).
    rewrite ES.
    assert (Hn : 0 <= Z.of_nat (length (r_calls R)) < 16) by lia.
    set (n := Z.of_nat (length (r_calls R))) in *. clearbody n.
    unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, SC_SIZE, REC_SIZE, REC_CALLS_MAX.
    split; [left; exists n; split; [lia | reflexivity]|].
    split; [lia|]. split; [lia|]. split; [lia | left; lia].
  - assert (ES : rec_slotA R = A_REC_SPILL).
    { unfold rec_slotA. destruct (Nat.ltb_spec (length (r_calls R)) 16); [lia | reflexivity]. }
    rewrite ES. unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, SC_SIZE, REC_SIZE.
    split; [right; reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity | right; reflexivity].
Qed.

(* added for sup_instance_verb: the argument count in the slot of the current call (arg_line's and arg_s's
   `aval_mem rd (c + CALL_OFF_NARGS) 4 m` premise), read off the representation *)
Section n. Variable B : asyms.
Lemma rec_repA_slot_nargs : forall ly S rd R fn As O, rec_repA B ly S rd (rec_record R fn As) O ->
  (length (r_calls R) <= 16)%nat -> aval_mem rd (rec_slotA R + CALL_OFF_NARGS) 4 (Z.of_nat (length As)).
Proof.
  intros ly S rd R fn As O (Q & HR & _) HL.
  pose proof HR as (_ & _ & _ & (_ & C2 & _ & C4 & C5 & _) & _).
  destruct (rec_slotA_entry R fn As HL) as [(k & Hk & Es) | (Es & Esp)].
  - destruct (nth_error (l_calls Q) k) as [P|] eqn:HP.
    + destruct (C4 k (fn, As) P Hk HP) as ((_ & _ & _ & _ & N & _) & _). rewrite Es. exact N.
    + exfalso. apply nth_error_None in HP.
      pose proof (proj1 (nth_error_Some (r_calls (rec_record R fn As)) k) ltac:(rewrite Hk; discriminate)). lia.
  - rewrite Es. pose proof C5 as (_ & _ & _ & _ & N & _). rewrite <- Esp in N. exact N.
Qed.

(* added for sup_instance_verb: every block the recorder owns is at least one byte (acall_at, aanswer_at and
   areply_at all bound the text's length below the block's size), which is what makes a fresh block's apartness
   say that its address is new *)
Lemma rec_repA_sizes : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> 1 <= snd pn.
Proof.
intros ly S rd R O (Q & HR & HO) pn Hpn. apply HO in Hpn. unfold lay_blocks in Hpn.
destruct HR as (_ & _ & _ & (Hc1 & Hc2 & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
apply in_app_or in Hpn as [Hpn | Hpn]; [|apply in_app_or in Hpn as [Hpn | Hpn]; [|apply in_app_or in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
  + destruct (Hc4 i c P Hc Hi) as ((_ & _ & HL & _ & _ & _ & H7) & _).
    apply In_nth_error in Hin as (k & Hk).
    destruct (nth_error (snd c) k) as [s|] eqn:Hs.
    * destruct (H7 k s pn Hs Hk) as (_ & _ & _ & Hsz & _). lia.
    * exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
  + exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- destruct Hsp as (_ & _ & HL & _ & _ & _ & H7). apply In_nth_error in Hpn as (k & Hk).
  destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs.
  + destruct (H7 k s pn Hs Hk) as (_ & _ & _ & Hsz & _). lia.
  + exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) k) ltac:(rewrite Hk; discriminate)). lia.
- unfold aanswer_at in Ha. destruct (r_answer R), (l_answer Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
  destruct Hpn as [<- | []]. destruct Ha as (_ & _ & _ & Hsz & _). lia.
- unfold areply_at in Hr. destruct (r_reply R) as [x|], (l_reply Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
  destruct Hpn as [<- | []]. destruct Hr as (_ & _ & _ & Hne & _ & Hsz & _).
  destruct x as [|b0 x']; [exfalso; exact (Hne eq_refl)|]. cbn [length] in Hsz. lia.
Qed.
End n.
