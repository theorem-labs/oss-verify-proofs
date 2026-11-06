(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the second half of the walk of sup_chain_clear on plugin-hostd/fuzz_command.asan
   (from the join of record()'s two arms to the tail jump into answer), in the walk style of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a run, a call through cl_callS, the return through
   jafter_call_keep_pi); the seed tables after lib/A/Prog/RecBTemplate.v,
   itself after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_chain_clear_s2.v, with its module paths and module names changed; 272 of its 378 lines of code are new or changed and 906 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/plugin-hostd/fuzz_command/lib/Prog/RecStep.v to the ASan
   representation lib/A/Prog/CmdRep.v (rec_repA / arep_at over a reader), for the walk of sup_chain_clear. *)
(* Modified by Theorem Labs, 2026-10: the keep lemmas for aval_mem, abytes_atR, astr_atR and acall_at and the
   block lemma arep_at_in follow proofs/plugin-hostd/fuzz_command/lib/A/Prog/RecBLemmas.v (aval_mem_agree_in,
   astr_atR_agree_in, acall_at_agree, acall_at_in, lay_blocks_in), restated with the keep premise in point form. *)
(* Modified by Theorem Labs, 2026-10: copied for sup_pin_accept's walk from the sup_chain_clear walk's
   lib/A/Prog/sup_chain_clear_s1.v and sup_chain_clear_s2.v (before they were in the tree), names
   prefixed spa_; the footprint is sup_pin_accept's (spa_FP). They go when a shared recorder library lands. *)

(* The recorder's representation read through a later state: the bytes it reads (g_rec, record.spill and the
   recorder's blocks), what a callee's journal keeps of them, and the block bookkeeping of the recorder posts. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the footprint of sup_pin_accept's contract (sup_pin_accept_c.v:90) *)
Definition spa_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

(* the bytes the representation reads besides the recorder's blocks: g_rec and record.spill *)
Definition spa_in_rec (a : Z) : Prop := A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.

(* every block of O is still live in bl' and keeps its bytes *)
Definition spa_keepsO (rd rd' : reader) (bl' : list (Z * Z)) (O : list (Z * Z)) : Prop :=
  forall pn, In pn O -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i).

(* ---- keep lemmas over a reader ---- *)

Lemma spa_aval_mem_keep : forall rd rd' a n v,
  aval_mem rd a n v -> (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma spa_abytes_keep : forall rd rd' a l,
  abytes_atR rd a l -> (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma spa_astr_keep : forall rd rd' p s,
  astr_atR rd p s -> (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H Hn] K. split; [|exact Hn].
  apply (spa_abytes_keep rd); [exact H|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply K. lia.
Qed.

Lemma spa_acall_keep : forall bl bl' rd rd' a c P,
  acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk) K KP.
  unfold acall_at. unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  split; [exact Hfn|]. split; [exact Hn|]. split; [exact Hl|].
  split; [apply (spa_aval_mem_keep rd); [exact Hb0 | intros x Hx; apply K; lia]|].
  split; [apply (spa_aval_mem_keep rd); [exact Hb1 | intros x Hx; apply K; lia]|].
  split; [exact Hnd|].
  intros k s pn Es Ep. destruct (Hk k s pn Es Ep) as (Hs & Hp0 & Hin & Hsz & Hstr).
  assert (Hkl : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  destruct (KP pn (nth_error_In P k Ep)) as [Hin' Kp].
  split; [apply (spa_aval_mem_keep rd); [exact Hs | intros x Hx; apply K; lia]|].
  split; [exact Hp0|]. split; [exact Hin'|]. split; [exact Hsz|].
  apply (spa_astr_keep rd); [exact Hstr|]. intros x Hx.
  apply (rd_agree_at rd rd' (fst pn) (snd pn)); [exact Kp | lia].
Qed.

Lemma spa_aanswer_keep : forall bl bl' rd rd' gr t q,
  aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q HA K KQ. revert HA KQ. unfold aanswer_at.
  destruct t as [s|]; destruct q as [pn|]; intros HA KQ; try contradiction.
  - destruct HA as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KQ pn (or_introl eq_refl)) as [Kin Kp].
    split; [apply (spa_aval_mem_keep rd); [exact N1 | intros y Hy; apply K; lia]|].
    split; [exact N2|]. split; [exact Kin|]. split; [exact N4|]. split; [|exact N6].
    apply (spa_astr_keep rd); [exact N5|]. intros y Hy.
    apply (rd_agree_at rd rd' (fst pn) (snd pn)); [exact Kp | lia].
  - apply (spa_aval_mem_keep rd); [exact HA | intros y Hy; apply K; lia].
Qed.

Lemma spa_areply_keep : forall bl bl' rd rd' gr t q,
  areply_at bl rd gr t q ->
  (forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY_SIZE + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  areply_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q HP K KQ. revert HP KQ. unfold areply_at. unfold OFF_REPLY, OFF_REPLY_SIZE in *.
  destruct t as [s|]; destruct q as [pn|]; intros HP KQ; try contradiction.
  - destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    destruct (KQ pn (or_introl eq_refl)) as [Kin Kp].
    split; [apply (spa_aval_mem_keep rd); [exact P1 | intros y Hy; apply K; lia]|].
    split; [apply (spa_aval_mem_keep rd); [exact P2 | intros y Hy; apply K; lia]|].
    split; [exact P3|]. split; [exact P4|]. split; [exact Kin|]. split; [exact P6|]. split; [|exact P8].
    apply (spa_abytes_keep rd); [exact P7|]. intros y Hy.
    apply (rd_agree_at rd rd' (fst pn) (snd pn)); [exact Kp | lia].
  - destruct HP as [P1 P2].
    split; [apply (spa_aval_mem_keep rd); [exact P1 | intros y Hy; apply K; lia]|].
    apply (spa_aval_mem_keep rd); [exact P2 | intros y Hy; apply K; lia].
Qed.

Lemma spa_ag1_scalars_keep : forall rd rd' gr R,
  ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R HX K. unfold ag1_scalars in *. unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  destruct HX as (X1 & X2 & X3 & X4 & X5 & X6).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  - apply (spa_aval_mem_keep rd); [exact X1 | intros x Hx; apply K; lia].
  - apply (spa_aval_mem_keep rd); [exact X2 | intros x Hx; apply K; lia].
  - apply (spa_aval_mem_keep rd); [exact X3 | intros x Hx; apply K; lia].
  - apply (spa_aval_mem_keep rd); [exact X4 | intros x Hx; apply K; lia].
  - apply (spa_aval_mem_keep rd); [exact X5 | intros x Hx; apply K; lia].
Qed.

(* ---- the blocks the representation names ---- *)

Lemma spa_acall_in : forall bl rd a c P pn, acall_at bl rd a c P -> In pn P -> In pn bl /\ fst pn <> 0.
Proof.
  intros bl rd a c P pn (_ & _ & Hl & _ & _ & _ & Hk) Hin.
  destruct (In_nth_error P pn Hin) as [k Ek].
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (Hk k s pn Es Ek) as (_ & H0 & H1 & _). split; assumption.
Qed.

Lemma spa_arep_in : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> In pn bl /\ fst pn <> 0.
Proof.
  intros bl rd gr sc R Q pn (_ & _ & _ & HC & HA & HP & _ & _) Hin.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP0 & Hpn).
    destruct (In_nth_error _ _ HP0) as [i Ei].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    exact (spa_acall_in _ _ _ _ _ _ (proj1 (C4 i c P Ec Ei)) Hpn).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (spa_acall_in _ _ _ _ _ _ C5 Hin)|].
    apply in_app_or in Hin as [Hin|Hin].
    + revert HA Hin. unfold aanswer_at.
      destruct (r_answer R); destruct (l_answer Q) as [pn'|]; intros HA Hin; cbn [oblk In] in Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HA as (_ & H0 & H1 & _). split; assumption.
    + revert HP Hin. unfold areply_at.
      destruct (r_reply R); destruct (l_reply Q) as [pn'|]; intros HP Hin; cbn [oblk In] in Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HP as (_ & _ & H0 & _ & H1 & _). split; assumption.
Qed.

(* ---- the representation, rebuilt around a new call table ---- *)

(* everything but the call table and the spill is kept: answer, reply, the scalars *)
Lemma spa_arep_rest : forall bl bl' rd rd' R R' Q Q',
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
  { apply (spa_aanswer_keep bl bl' rd rd' A_G_REC _ _ HA).
    - intros x Hx. apply K. unfold OFF_ANSWER in Hx. lia.
    - intros pn Hpn. apply KO. apply in_or_app. left. exact Hpn. }
  split.
  { apply (spa_areply_keep bl bl' rd rd' A_G_REC _ _ HP).
    - intros x Hx. apply K. unfold OFF_REPLY, OFF_REPLY_SIZE in Hx. lia.
    - intros pn Hpn. apply KO. apply in_or_app. right. exact Hpn. }
  split; [|exact HW'].
  apply (spa_ag1_scalars_keep rd rd' A_G_REC R' HX'). intros x Hx. apply K. lia.
Qed.

Lemma spa_arep_keep : forall bl bl' rd rd' R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (forall a, spa_in_rec a -> rd' a = rd a) ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
  intros bl bl' rd rd' R Q HR K KQ.
  pose proof HR as (_ & _ & _ & HC & _ & _ & _ & HW).
  apply (spa_arep_rest bl bl' rd rd' R R Q Q HR); try reflexivity.
  - intros a Ha. apply K. unfold spa_in_rec, REC_SIZE. lia.
  - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn.
  - destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (spa_aval_mem_keep rd); [exact C3 | intros x Hx; apply K; unfold spa_in_rec, OFF_NCALLS, REC_SIZE in *; lia].
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (spa_acall_keep bl bl' rd rd' _ c P Hc).
      * intros x Hx. apply K. unfold spa_in_rec, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + apply (spa_acall_keep bl bl' rd rd' _ _ _ C5).
      * intros x Hx. apply K. unfold spa_in_rec, CALL_SIZE, SC_SIZE in *. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - exact HW.
Qed.

Section r. Variable B : asyms.
(* the representation survives any change outside g_rec, record.spill and the recorder's blocks *)
Lemma spa_rep_keep : forall ly S rd ly' S' rd' R O,
  rec_repA B ly S rd R O -> (forall a, spa_in_rec a -> rd' a = rd a) -> spa_keepsO rd rd' (ablocks B ly' S') O ->
  rec_repA B ly' S' rd' R O.
Proof.
  intros ly S rd ly' S' rd' R O (Q & HR & HO) K KO. unfold spa_keepsO in KO.
  exists Q. split; [|exact HO].
  apply (spa_arep_keep _ _ rd rd' R Q HR K). intros pn Hpn. apply KO. apply HO. exact Hpn.
Qed.

Lemma spa_rep_blocks : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O ->
  In pn (ablocks B ly S) /\ fst pn <> 0 /\ iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE.
Proof.
  intros ly S rd R O (Q & HR & HO) pn Hpn. apply HO in Hpn.
  destruct (spa_arep_in _ _ _ _ _ _ pn HR Hpn) as [H1 H2].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & (_ & HAP)).
  destruct (HAP pn Hpn) as [H3 H4]. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma spa_rep_answer : forall ly S rd R O, rec_repA B ly S rd R O ->
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
End r.

(* a member of a filtered list is a member of the list (the filter answer_c.v's footprint uses) *)
Lemma spa_filter_in : forall (old : Z) (l : list (Z * Z)) x, In x (filter (fun pn => fst pn =? old) l) -> In x l.
Proof.
intros old l x. induction l as [|a l IH]; intros H; cbn in H; [exact H|].
repeat match type of H with context [match ?d with left _ => _ | right _ => _ end] => destruct d end;
repeat match type of H with context [if ?b then _ else _] => destruct b end;
first [ destruct H as [<- | H]; [left; reflexivity | right; exact (IH H)] | right; exact (IH H) ].
Qed.

(* the block bookkeeping of the post, over the block lists of the entry (bl0), the join (blc), answer's entry (bl4)
   and the end (bl5) *)
Lemma spa_post_lists : forall (bl0 blc bl4 bl5 O O1 O' : list (Z * Z)) pnew p1 p2 old,
(forall pn, In pn bl0 -> ~ In pn O -> In pn blc) ->
(forall pn, In pn blc -> In pn bl0) ->
(forall pn, In pn O1 -> In pn O) ->
(forall pn, In pn O -> In pn blc -> In pn O1) ->
(forall pn, In pn O1 -> In pn blc) ->
~ In pnew blc ->
(forall pn, In pn bl4 <-> pn = pnew \/ In pn blc) ->
~ In p1 bl4 -> ~ In p2 bl4 -> p1 <> p2 ->
(forall pn, In pn bl5 <-> (In pn bl4 /\ fst pn <> old) \/ pn = p1 \/ pn = p2) ->
(forall pn, In pn O' <-> (In pn (O1 ++ [pnew]) /\ fst pn <> old) \/ pn = p1) ->
(forall pn, In pn bl4 -> fst pn = old -> In pn (O1 ++ [pnew])) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn bl0) /\
In p2 bl5 /\
(In p2 bl0 -> In p2 O) /\
~ In p2 O' /\
(forall pn, In pn bl0 -> ~ In pn O -> In pn bl5 /\ In pn bl4) /\
(forall pn, In pn bl5 -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = p2).
Proof.
intros bl0 blc bl4 bl5 O O1 O' pnew p1 p2 old HB2 HB1 HO1 HO2 HO1c Hnew H4 Hp1 Hp2 H12 H5 HO' Hold.
assert (Hdec : forall pn (l : list (Z * Z)), In pn l \/ ~ In pn l)
  by (intros pn l; destruct (in_dec (fun x y : Z * Z => decide (x = y)) pn l); tauto).
assert (HinO : forall pn, In pn bl0 -> ~ In pn bl4 -> In pn O).
{ intros pn H0 Hn4. destruct (Hdec pn O) as [H|H]; [exact H|]. exfalso. apply Hn4. apply H4. right. exact (HB2 pn H0 H). }
assert (Hnew0 : In pnew bl0 -> In pnew O).
{ intros H0. destruct (Hdec pnew O) as [H|H]; [exact H | exfalso; exact (Hnew (HB2 _ H0 H))]. }
split; [|split; [|split; [|split; [|split]]]].
- intros pn Hpn. apply HO' in Hpn as [(Hin & _) | ->].
  + apply in_app_or in Hin as [Hin | [<- | []]]; [left; exact (HO1 _ Hin)|].
    destruct (Hdec pnew bl0) as [H|H]; [left; exact (Hnew0 H) | right; exact H].
  + destruct (Hdec p1 bl0) as [H|H]; [left; exact (HinO _ H Hp1) | right; exact H].
- apply H5. right; right. reflexivity.
- intros H0. exact (HinO _ H0 Hp2).
- intros Hin. apply HO' in Hin as [(Hin & _) | E]; [|exact (H12 (eq_sym E))].
  apply in_app_or in Hin as [Hin | [E | []]].
  + apply Hp2. apply H4. right. exact (HO1c _ Hin).
  + apply Hp2. apply H4. left. symmetry. exact E.
- intros pn H0 HnO. assert (Hc : In pn blc) by exact (HB2 _ H0 HnO).
  assert (H4' : In pn bl4) by (apply H4; right; exact Hc).
  split; [|exact H4']. apply H5. left. split; [exact H4'|]. intros Eo.
  pose proof (Hold _ H4' Eo) as Hin. apply in_app_or in Hin as [Hin | [E | []]].
  + exact (HnO (HO1 _ Hin)).
  + subst pn. exact (Hnew Hc).
- intros pn Hpn. apply H5 in Hpn as [(Hin4 & Hne) | [-> | ->]].
  + apply H4 in Hin4 as [-> | Hc].
    * right; left. apply HO'. left. split; [apply in_or_app; right; left; reflexivity | exact Hne].
    * destruct (Hdec pn O) as [HinO' | HnO].
      -- right; left. apply HO'. left. split; [apply in_or_app; left; exact (HO2 _ HinO' Hc) | exact Hne].
      -- left. split; [exact (HB1 _ Hc) | exact HnO].
  + right; left. apply HO'. right. reflexivity.
  + right; right. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.

Lemma spa_in_recPG : forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
Exists (in_zr a) recb_PG.
Proof.
intros a [Ha | Ha]; apply Exists_exists.
- exists (A_G_REC, REC_SIZE). split; [left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
- exists (A_REC_SPILL, SC_SIZE). split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
Qed.

(* g_rec's and record.spill's bytes are none of the runtime's statics (HB's ts_owned) and not the errno cell *)
Lemma spa_rec_unowned : forall a, spa_in_rec a ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB). unfold spa_in_rec in Ha.
split.
- intros HE. apply Exists_exists in HE as ([lo n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  assert (Hb1 : forallb (fun r => (0x5e3b00 <=? fst r) || (fst r + snd r <=? 0x5e3740)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  assert (Hb2 : forallb (fun r => (0x5e3c18 <=? fst r) || (fst r + snd r <=? 0x5e3be0)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hb1 _ Hin) as Hq1. pose proof (proj1 (forallb_forall _ _) Hb2 _ Hin) as Hq2.
  cbn beta in Hq1, Hq2. cbn [fst snd] in Hq1, Hq2.
  unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha.
  apply Bool.orb_true_iff in Hq1 as [Hq1 | Hq1]; apply Z.leb_le in Hq1;
  apply Bool.orb_true_iff in Hq2 as [Hq2 | Hq2]; apply Z.leb_le in Hq2; lia.
- unfold TFIB_ERRNO, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *. lia.
Qed.

(* a callee whose footprint misses a byte of g_rec / record.spill leaves it as it was (the journal's image clause) *)
Lemma spa_rec_kept : forall STK sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly' S' W' mem' md' k a,
ajournal SEGS B STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP1 -> spa_in_rec a -> ~ inFP FP1 a -> rdW W' mem' a = rdW Wc memc a.
Proof.
intros STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k a HJ Hsk Ha Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (spa_rec_unowned a Ha) as [Ho He].
apply F3; [| exact Ho | exact He | exact (fp_spares_closed FP1 a Hsk Hn)].
apply cmd_prog_img. apply spa_in_recPG. exact Ha.
Qed.

(* a live block is apart from g_rec and record.spill (no block byte is an image byte) *)
Lemma spa_blk_apart : forall ly S (W : world SEGS) mem md p n, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
iv_apart p n A_G_REC REC_SIZE /\ iv_apart p n A_REC_SPILL SC_SIZE.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4096 & _ & _ & _ & _ & Hnr).
assert (Hn0 : 0 <= n) by lia.
pose proof (req_size_pos n Hn0) as [R1 R2].
assert (HI : forall a, p <= a < p + req_size n -> ~ in_img SEGS a)
  by (intros a Ha; apply (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin); lia).
unfold iv_apart. split.
- destruct (Z.le_gt_cases (p + n) A_G_REC) as [H|H]; [left; exact H|].
  destruct (Z.le_gt_cases (A_G_REC + REC_SIZE) p) as [H'|H']; [right; exact H'|]. exfalso.
  apply (HI (Z.max p A_G_REC)); [lia|]. apply cmd_prog_img. apply spa_in_recPG. left. unfold REC_SIZE in *. lia.
- destruct (Z.le_gt_cases (p + n) A_REC_SPILL) as [H|H]; [left; exact H|].
  destruct (Z.le_gt_cases (A_REC_SPILL + SC_SIZE) p) as [H'|H']; [right; exact H'|]. exfalso.
  apply (HI (Z.max p A_REC_SPILL)); [lia|]. apply cmd_prog_img. apply spa_in_recPG. right. unfold SC_SIZE in *. lia.
Qed.

(* a block live across a callee whose footprint lies in g_rec / record.spill keeps its bytes *)
Lemma spa_blk_kept : forall STK sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly' S' W' mem' md' k p n i,
ajournal SEGS B STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k ->
AR SEGS B lyc Sc Wc memc mdc ->
(forall a, inFP FP1 a -> spa_in_rec a) ->
In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly' S') -> 0 <= i < n ->
rdW W' mem' (p + i) = rdW Wc memc (p + i).
Proof.
intros STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k p n i HJ HAR HFP Hin Hin' Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (req_size_pos n ltac:(lia)) as [R1 R2].
apply (F2 p n i); [exact Hin | exact Hin' | lia |].
intros Hf. apply HFP in Hf.
apply (blk_img SEGS B LAWS lyc Sc Wc memc mdc p n (p + i) HAR Hin); [lia|].
apply cmd_prog_img. apply spa_in_recPG. exact Hf.
Qed.

(* no read-only byte is in the contract's footprint (arodata_ok_journalP's premise) *)
Lemma spa_ro_off : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP (spa_FP O) a.
Proof.
intros ly S W mem md O HAR HOS a Hro (r & Hr & Ha).
destruct (cmd_ro_prog_apart a Hro) as [Himg Hnp].
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- apply Hnp. apply spa_in_recPG. left. exact Ha.
- apply Hnp. apply spa_in_recPG. right. exact Ha.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  exact (blk_img SEGS B LAWS ly S W mem md p n a HAR (HOS _ Hin) Ha Himg).
Qed.

(* two live blocks with the same start are the same block (the allocator record keeps them disjoint) *)
Lemma spa_same_start : forall ly S (W : world SEGS) mem md a b, AR SEGS B ly S W mem md ->
In a (ablocks B ly S) -> In b (ablocks B ly S) -> fst a = fst b -> a = b.
Proof.
intros ly S W mem md [pa na] [pb nb] HAR Ha Hb E. cbn [fst] in E. subst pb.
destruct (decide ((pa, na) = (pa, nb))) as [Heq | Hne]; [exact Heq|]. exfalso.
pose proof (sep_blocks SEGS B LAWS ly S W mem md pa na pa nb HAR Ha Hb Hne) as Hd.
destruct (al_blocks _ _ LAWS ly S W mem md pa na HAR Ha) as (_ & _ & _ & _ & _ & _ & Hna).
destruct (al_blocks _ _ LAWS ly S W mem md pa nb HAR Hb) as (_ & _ & _ & _ & _ & _ & Hnb).
pose proof (req_size_pos na ltac:(lia)) as [Ra _]. pose proof (req_size_pos nb ltac:(lia)) as [Rb _].
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
End e.
End f.
End d.
