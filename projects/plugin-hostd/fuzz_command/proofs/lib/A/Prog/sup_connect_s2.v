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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Arithmetic facts of the layout *)

(* a slot of g_rec's call table: apart from ncalls, inside g_rec; record.spill inside its 56 bytes; all of them
   inside cmd_PG *)
Lemma scn_slot_disj : forall i, 0 <= i < REC_CALLS_MAX ->
  iv_apart (A_G_REC + OFF_CALLS + CALL_SIZE * i) CALL_SIZE (A_G_REC + OFF_NCALLS) 4 /\
  A_G_REC <= A_G_REC + OFF_CALLS + CALL_SIZE * i /\
  A_G_REC + OFF_CALLS + CALL_SIZE * i + CALL_SIZE <= A_G_REC + 960 /\
  (forall a, A_G_REC + OFF_CALLS + CALL_SIZE * i <= a < A_G_REC + OFF_CALLS + CALL_SIZE * i + CALL_SIZE ->
     inFP cmd_PG a) /\
  (forall a, A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4 -> inFP cmd_PG a) /\
  (forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> A_REC_SPILL <= a < A_REC_SPILL + 56 /\ inFP cmd_PG a).
Proof.
  intros i Hi. unfold REC_CALLS_MAX, iv_apart, OFF_CALLS, OFF_NCALLS, CALL_SIZE, SC_SIZE in *.
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; lia]|].
  split; [intros a Ha; exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; lia]|].
  intros a Ha. split; [lia|].
  exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

(* the two fields an argument step writes lie inside the slot, apart from each other *)
Lemma scn_field_in : forall c m, 0 <= m < REC_ARGS_MAX ->
  c <= c + CALL_OFF_NARGS /\ c + CALL_OFF_NARGS + 4 <= c + CALL_OFF_ARGS + 8 * m /\
  c + CALL_OFF_ARGS + 8 * m + 8 <= c + CALL_SIZE /\ c + CALL_OFF_FN + 4 <= c + CALL_OFF_NARGS.
Proof. intros c m Hm. unfold REC_ARGS_MAX, CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE, CALL_OFF_FN in *. lia. Qed.

(* the canonical line is no longer than the line (lib/Prog/RecFacts.v:180 canon_length) *)
Lemma scn_canon_len : forall T, Z.of_nat (length (canon T)) <= Z.of_nat (length T).
Proof. intros T. pose proof (canon_length T). lia. Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Model facts *)

Lemma scn_record_spill_eq : forall R x fn A, length (r_calls R) = 16%nat ->
  rec_record (set_spill R x) fn A = rec_record R fn A.
Proof.
  intros R x fn A Hn. rewrite (RecStep.rec_record_full R fn A Hn).
  rewrite (RecStep.rec_record_full (set_spill R x) fn A Hn). reflexivity.
Qed.

Lemma scn_lay_lt : forall Q,
  lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q.
Proof.
  intros Q. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
  rewrite !app_nil_r. reflexivity.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Keeping the representation under a reader that agrees on the bytes it reads *)

Lemma scn_aval_keep : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma scn_bytes_keep : forall (rd rd' : reader) a l, abytes_atR rd a l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma scn_str_keep : forall (rd rd' : reader) p s, astr_atR rd p s ->
  (forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H1 H2] K. split; [|exact H2]. apply (scn_bytes_keep rd); [exact H1|].
  intros i Hi. apply K. rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.

Lemma scn_call_keep : forall bl bl' (rd rd' : reader) a c P,
  acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk) K KP.
  unfold acall_at.
  split; [exact Hfn|]. split; [exact Hn|]. split; [exact Hl|].
  split; [apply (scn_aval_keep rd); [exact Hb0 | intros x Hx; apply K;
          unfold CALL_SIZE, CALL_OFF_FN in *; lia]|].
  split; [apply (scn_aval_keep rd); [exact Hb1 | intros x Hx; apply K;
          unfold CALL_SIZE, CALL_OFF_NARGS in *; lia]|].
  split; [exact Hnd|].
  intros k s pn Es Ep. destruct (Hk k s pn Es Ep) as (Hs & Hq0 & Hq & Hqs & Hstr).
  assert (Hkl : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  assert (Hpn : In pn P) by (eapply nth_error_In; exact Ep).
  destruct (KP pn Hpn) as [Kin Kp].
  split; [apply (scn_aval_keep rd); [exact Hs | intros x Hx; apply K;
          unfold CALL_SIZE, CALL_OFF_ARGS in *; lia]|].
  split; [exact Hq0|]. split; [exact Kin|]. split; [exact Hqs|].
  apply (scn_str_keep rd); [exact Hstr|]. intros i Hi. apply Kp. lia.
Qed.

Lemma scn_call_pn : forall bl (rd : reader) a c P pn, acall_at bl rd a c P -> In pn P ->
  fst pn <> 0 /\ 1 <= snd pn /\ In pn bl.
Proof.
  intros bl rd a c P pn (_ & _ & HL & _ & _ & _ & HK) Hin.
  destruct (In_nth_error P pn Hin) as [k Ek].
  assert (Hk : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (HK k s pn Es Ek) as (_ & H0 & H1 & H2 & _). split; [exact H0|]. split; [lia | exact H1].
Qed.

(* every block of the recorder is live, non-null and at least one byte long *)
Lemma scn_lay_facts : forall bl (rd : reader) gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) ->
  fst pn <> 0 /\ 1 <= snd pn /\ In pn bl.
Proof.
  intros bl rd gr sc R Q pn (_ & _ & _ & HC & HA & HP & _ & _) Hin.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP0 & Hpn).
    destruct (In_nth_error _ _ HP0) as [i Ei].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    exact (scn_call_pn _ _ _ _ _ _ (proj1 (C4 i c P Ec Ei)) Hpn).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (scn_call_pn _ _ _ _ _ _ C5 Hin)|].
    unfold aanswer_at, areply_at in *.
    apply in_app_or in Hin as [Hin|Hin].
    + revert HA Hin. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [[p k]|]; cbn [oblk In];
        intros HA Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HA as (_ & N2 & N3 & N4 & _). cbn [fst snd] in *.
      split; [exact N2|]. split; [lia | exact N3].
    + revert HP Hin. destruct (r_reply R) as [y|]; destruct (l_reply Q) as [[p k]|]; cbn [oblk In];
        intros HP Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HP as (_ & _ & P3 & P4 & P5 & P6 & _). cbn [fst snd] in *.
      split; [exact P3|]. split; [|exact P5].
      destruct y as [|b y]; [exfalso; exact (P4 eq_refl) | cbn [length] in P6; lia].
Qed.

Lemma scn_lay_in_bl : forall bl (rd : reader) gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) ->
  In pn bl.
Proof. intros bl rd gr sc R Q pn H Hin. exact (proj2 (proj2 (scn_lay_facts bl rd gr sc R Q pn H Hin))). Qed.

(* the answer, the reply and the scalar fields, kept *)
Lemma scn_rest_keep : forall bl bl' (rd rd' : reader) gr R ans rep,
  aanswer_at bl rd gr (r_answer R) ans -> areply_at bl rd gr (r_reply R) rep -> ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 912 <= x < gr + 960 -> rd' x = rd x) ->
  (forall pn, In pn (oblk ans ++ oblk rep) -> In pn bl' /\
     forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  aanswer_at bl' rd' gr (r_answer R) ans /\ areply_at bl' rd' gr (r_reply R) rep /\ ag1_scalars rd' gr R.
Proof.
  intros bl bl' rd rd' gr R ans rep HA HP HX KR KQ.
  unfold aanswer_at, areply_at, ag1_scalars in *.
  unfold OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  split; [|split].
  - revert HA KQ. destruct (r_answer R) as [t|]; destruct ans as [[p k]|]; intros HA KQ; try contradiction.
    + destruct HA as (N1 & N2 & N3 & N4 & N5 & N6). cbn [fst snd] in *.
      destruct (KQ (p, k) ltac:(cbn; left; reflexivity)) as [Kin Kp]. cbn [fst snd] in Kp.
      split; [apply (scn_aval_keep rd); [exact N1 | intros x Hx; apply KR; lia]|].
      split; [exact N2|]. split; [exact Kin|]. split; [exact N4|].
      split; [apply (scn_str_keep rd); [exact N5 | intros i Hi; apply Kp; lia] | exact N6].
    + apply (scn_aval_keep rd); [exact HA | intros x Hx; apply KR; lia].
  - revert HP KQ. destruct (r_reply R) as [y|]; destruct rep as [[p k]|]; intros HP KQ; try contradiction.
    + destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). cbn [fst snd] in *.
      destruct (KQ (p, k) ltac:(apply in_or_app; right; cbn; left; reflexivity)) as [Kin Kp].
      cbn [fst snd] in Kp.
      split; [apply (scn_aval_keep rd); [exact P1 | intros x Hx; apply KR; lia]|].
      split; [apply (scn_aval_keep rd); [exact P2 | intros x Hx; apply KR; lia]|].
      split; [exact P3|]. split; [exact P4|]. split; [exact Kin|]. split; [exact P6|].
      split; [apply (scn_bytes_keep rd); [exact P7 | intros i Hi; apply Kp; lia] | exact P8].
    + destruct HP as [P1 P2].
      split; [apply (scn_aval_keep rd); [exact P1 | intros x Hx; apply KR; lia]|].
      apply (scn_aval_keep rd); [exact P2 | intros x Hx; apply KR; lia].
  - destruct HX as (X1 & X2 & X3 & X4 & X5 & X6).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
    + apply (scn_aval_keep rd); [exact X1 | intros x Hx; apply KR; lia].
    + apply (scn_aval_keep rd); [exact X2 | intros x Hx; apply KR; lia].
    + apply (scn_aval_keep rd); [exact X3 | intros x Hx; apply KR; lia].
    + apply (scn_aval_keep rd); [exact X4 | intros x Hx; apply KR; lia].
    + apply (scn_aval_keep rd); [exact X5 | intros x Hx; apply KR; lia].
Qed.

(* one argument appended to a call (plain RecStep.v:442-485 call_at_arg) *)
Lemma scn_call_arg : forall bl bl' (rd rd' : reader) e fn A P s p k,
  acall_at bl rd e (fn, A) P -> (length A < 6)%nat ->
  aval_mem rd' (e + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
  aval_mem rd' (e + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
  (forall a, e <= a < e + CALL_SIZE -> ~ (e + CALL_OFF_NARGS <= a < e + CALL_OFF_NARGS + 4) ->
     ~ (e + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < e + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
     rd' a = rd a) ->
  (forall pn, In pn P -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  ~ In p (map fst P) -> p <> 0 -> In (p, k) bl' -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 ->
  astr_atR rd' p s ->
  acall_at bl' rd' e (fn, A ++ [s]) (P ++ [(p, k)]).
Proof.
  intros bl bl' rd rd' e fn A P s p k (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk) H6 BN BS K KP Hfr Hp0 Hin Hsz Hx.
  cbn [fst snd] in *.
  unfold acall_at. cbn [fst snd].
  split; [exact Hfn|]. split; [rewrite length_app; cbn [length]; lia|].
  split; [rewrite !length_app, Hl; reflexivity|].
  split; [apply (scn_aval_keep rd); [exact Hb0 | intros a Ha; apply K;
          unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia]|].
  split; [rewrite length_app, Nat2Z.inj_add; exact BN|].
  split; [exact (RecStep.nodup_fst_snoc P p k Hnd Hfr)|].
  intros j s' pn Es Ep.
  destruct (Nat.lt_ge_cases j (length A)) as [Hj|Hj].
  - rewrite nth_error_app1 in Es by exact Hj. rewrite nth_error_app1 in Ep by (rewrite Hl; exact Hj).
    destruct (Hk j s' pn Es Ep) as (Hs & Hq0 & Hq & Hqs & Hstr).
    assert (Hpn : In pn P) by (eapply nth_error_In; exact Ep).
    destruct (KP pn Hpn) as [Kin Kp].
    split; [apply (scn_aval_keep rd); [exact Hs | intros a Ha; apply K;
            unfold CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia]|].
    split; [exact Hq0|]. split; [exact Kin|]. split; [exact Hqs|].
    apply (scn_str_keep rd); [exact Hstr|]. intros i Hi. apply Kp. lia.
  - destruct (Nat.eq_dec j (length A)) as [->|Hne].
    + rewrite nth_error_app2, Nat.sub_diag in Es by lia. cbn in Es. injection Es as <-.
      rewrite nth_error_app2 in Ep by (rewrite Hl; lia). rewrite Hl, Nat.sub_diag in Ep. cbn in Ep.
      injection Ep as <-.
      cbn [fst snd]. split; [exact BS|]. split; [exact Hp0|]. split; [exact Hin|]. split; [exact Hsz | exact Hx].
    + exfalso. assert (N : nth_error (A ++ [s]) j = None)
        by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
      rewrite N in Es. discriminate.
Qed.

(* a fresh block apart from every live block is none of the recorder's blocks *)
Lemma scn_fresh_not_lay : forall bl (rd : reader) gr sc R Q p k, arep_at bl rd gr sc R Q -> 1 <= k ->
  Forall (fun qk => iv_apart p k (fst qk) (snd qk)) bl -> ~ In p (map fst (lay_blocks Q)).
Proof.
  intros bl rd gr sc R Q p k HR Hk HF Hq. apply in_map_iff in Hq as (pn & E & Hq).
  destruct (scn_lay_facts _ _ _ _ _ _ pn HR Hq) as (_ & H1 & Hb).
  assert (Ha : iv_apart p k (fst pn) (snd pn)) by (rewrite Forall_forall in HF; exact (HF pn Hb)).
  unfold iv_apart in Ha. lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* (1) record(), table arm: ncalls := n + 1, c->fn := fn, c->nargs := 0 for c the n-th slot *)
Lemma scn_record_lt : forall bl (rd rd' : reader) R Q n c fn,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  length (r_calls R) = n -> (n < 16)%nat -> 0 <= fn < REC_FN_COUNT ->
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat n + 1) ->
  aval_mem rd' (c + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 0 ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
              exists pn, In pn bl /\ In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn) ->
     ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + CALL_SIZE) -> rd' a = rd a) ->
  arep_at bl rd' A_G_REC A_REC_SPILL (rec_record R fn [])
    (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
  intros bl rd rd' R Q n c fn HR Hn Hlt Hfn Hc BN BF BA K. subst n c.
  rewrite (RecStep.rec_record_lt R fn [] Hlt).
  pose proof HR as (S1 & S2 & S3 & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  pose proof HW as [HND HAP].
  assert (KQ : forall pn, In pn (lay_blocks Q) ->
            In pn bl /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
  { intros pn Hpn. destruct (scn_lay_facts _ _ _ _ _ _ pn HR Hpn) as (_ & _ & Hbl).
    split; [exact Hbl|]. intros i Hi. destruct (HAP pn Hpn) as [A1 A2].
    apply K; [right; right; exists pn; split; [exact Hbl | split; [exact Hpn | lia]] | |];
      unfold iv_apart, REC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia. }
  assert (KR : forall x, A_G_REC <= x < A_G_REC + REC_SIZE ->
            ~ (A_G_REC + OFF_NCALLS <= x < A_G_REC + OFF_NCALLS + 4) ->
            ~ (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) <= x <
               A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_SIZE) -> rd' x = rd x).
  { intros x H1 H2 H3. apply K; [left; exact H1 | exact H2 | exact H3]. }
  assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd' x = rd x).
  { intros x Hx. apply K; [right; left; exact Hx | |];
      unfold iv_apart, REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia. }
  assert (KO : forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
  { intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
  destruct (scn_rest_keep bl bl rd rd' A_G_REC R (l_answer Q) (l_reply Q) HA HP HX
              ltac:(intros x Hx; apply KR; unfold REC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia) KO)
    as (RA & RP & RX).
  unfold arep_at.
  refine (conj S1 (conj S2 (conj S3 (conj _ (conj RA (conj RP (conj RX _))))))).
  - unfold ag1_calls. cbn [set_calls r_calls r_spill l_calls l_spill].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ C6))))).
    + rewrite length_app. cbn [length]. lia.
    + rewrite !length_app, C2. reflexivity.
    + rewrite length_app, Nat2Z.inj_add. exact BN.
    + intros i c P Ec EP.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      * rewrite nth_error_app1 in Ec by exact Hi. rewrite nth_error_app1 in EP by (rewrite C2; exact Hi).
        destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
        apply (scn_call_keep bl bl rd rd'); [exact Hc | |].
        -- intros x Hx. apply KR; unfold REC_SIZE, OFF_CALLS, OFF_NCALLS, CALL_SIZE in *; lia.
        -- intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
           exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
      * destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
        -- rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
           rewrite nth_error_app2 in EP by lia. rewrite C2, Nat.sub_diag in EP. cbn in EP. injection EP as <-.
           split; [|constructor].
           unfold acall_at. cbn [fst snd length].
           split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
           split; [exact BF|]. split; [exact BA|]. split; [constructor|].
           intros k s pn Es. destruct k; discriminate.
        -- exfalso. assert (N : nth_error (r_calls R ++ [(fn, [])]) i = None)
             by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
           rewrite N in Ec. discriminate.
    + apply (scn_call_keep bl bl rd rd'); [exact C5 | |].
      * intros x Hx. apply KS. unfold CALL_SIZE, SC_SIZE in *. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - unfold ag1_own in *. rewrite scn_lay_lt. exact HW.
Qed.

(* (2) record(), spill arm (after rec_calls_free emptied the spill): c->fn := fn, c->nargs := 0 for c the spill *)
Lemma scn_record_full : forall bl (rd rd' : reader) R Q fn,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  length (r_calls R) = 16%nat -> snd (r_spill R) = [] -> 0 <= fn < REC_FN_COUNT ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
              exists pn, In pn bl /\ In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn) ->
     ~ (A_REC_SPILL <= a < A_REC_SPILL + CALL_SIZE) -> rd' a = rd a) ->
  arep_at bl rd' A_G_REC A_REC_SPILL (rec_record R fn []) Q.
Proof.
  intros bl rd rd' R Q fn HR Hn Hsp Hfn BF BA K.
  rewrite (RecStep.rec_record_full R fn [] Hn).
  pose proof HR as (S1 & S2 & S3 & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  pose proof HW as [HND HAP].
  assert (Hls : l_spill Q = []).
  { destruct C5 as (_ & _ & HL & _). apply length_zero_iff_nil. rewrite HL, Hsp. reflexivity. }
  assert (KQ : forall pn, In pn (lay_blocks Q) ->
            In pn bl /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
  { intros pn Hpn. destruct (scn_lay_facts _ _ _ _ _ _ pn HR Hpn) as (_ & _ & Hbl).
    split; [exact Hbl|]. intros i Hi. destruct (HAP pn Hpn) as [A1 A2].
    apply K; [right; right; exists pn; split; [exact Hbl | split; [exact Hpn | lia]] |];
      unfold iv_apart, SC_SIZE, CALL_SIZE in *; lia. }
  assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> rd' x = rd x).
  { intros x Hx. apply K; [left; exact Hx |]. unfold iv_apart, REC_SIZE, SC_SIZE, CALL_SIZE in *; lia. }
  assert (KO : forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
  { intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
  destruct (scn_rest_keep bl bl rd rd' A_G_REC R (l_answer Q) (l_reply Q) HA HP HX
              ltac:(intros x Hx; apply KG; unfold REC_SIZE; lia) KO)
    as (RA & RP & RX).
  unfold arep_at.
  refine (conj S1 (conj S2 (conj S3 (conj _ (conj RA (conj RP (conj RX HW))))))).
  unfold ag1_calls. cbn [set_spill r_calls r_spill fst snd].
  refine (conj C1 (conj C2 (conj _ (conj _ (conj _ _))))).
  - apply (scn_aval_keep rd); [exact C3 | intros x Hx; apply KG; unfold OFF_NCALLS, REC_SIZE in *; lia].
  - intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
    apply (scn_call_keep bl bl rd rd'); [exact Hc | |].
    + intros x Hx. apply KG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
    + intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
      exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
  - rewrite Hls. unfold acall_at. cbn [fst snd length].
    split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
    split; [exact BF|]. split; [exact BA|]. split; [constructor|].
    intros k s pn Es. destruct k; discriminate.
  - constructor.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* (3) one argument appended to the slot being built: nargs := m + 1, args[m] := p, with p a fresh block of k bytes
   that holds s. Table arm. *)
Lemma scn_append_call : forall bl bl' (rd rd' : reader) R fn A l0 P ls la lr c s p k,
  arep_at bl rd A_G_REC A_REC_SPILL (rec_record R fn A) (RLay (l0 ++ [P]) ls la lr) ->
  (length (r_calls R) < 16)%nat ->
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
  (length A < 6)%nat ->
  p <> 0 -> astr_atR rd' p s -> Z.of_nat (length s) <= LMAX -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 ->
  Forall (fun qk => iv_apart p k (fst qk) (snd qk)) bl ->
  iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
  aval_mem rd' (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
              exists pn, In pn bl /\ In pn (lay_blocks (RLay (l0 ++ [P]) ls la lr)) /\
                fst pn <= a < fst pn + snd pn) ->
     ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
     ~ (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
     rd' a = rd a) ->
  (forall pn, In pn bl -> In pn bl') -> In (p, k) bl' ->
  arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R fn (A ++ [s])) (RLay (l0 ++ [P ++ [(p, k)]]) ls la lr).
Proof.
  intros bl bl' rd rd' R fn A l0 P ls la lr c s p k HR Hn Hc H6 Hp0 Hx Hlx Hsz HF Ha1 Ha2 BN BS K Hbl Hin.
  subst c.
  rewrite (RecStep.rec_record_lt R fn A Hn) in HR. rewrite (RecStep.rec_record_lt R fn (A ++ [s]) Hn).
  assert (Hfr : ~ In p (map fst (lay_blocks (RLay (l0 ++ [P]) ls la lr))))
    by (apply (scn_fresh_not_lay bl rd _ _ _ _ p k HR); [lia | exact HF]).
  pose proof HR as (S1 & S2 & S3 & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  destruct HW as [HND HAP].
  cbn [set_calls r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply] in C1, C2, C3, C4, C5, C6, HA, HP.
  assert (KQ : forall pn, In pn (lay_blocks (RLay (l0 ++ [P]) ls la lr)) ->
            In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
  { intros pn Hpn. destruct (scn_lay_facts _ _ _ _ _ _ pn HR Hpn) as (_ & _ & Hb).
    split; [exact (Hbl pn Hb)|]. intros i Hi. destruct (HAP pn Hpn) as [A1 A2].
    apply K; [right; right; exists pn; split; [exact Hb | split; [exact Hpn | lia]] | |];
      unfold iv_apart, REC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia. }
  assert (MB : forall pn, In pn P -> In pn (lay_blocks (RLay (l0 ++ [P]) ls la lr))).
  { intros pn Hpn. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply in_or_app. left.
    rewrite concat_app. apply in_or_app. right. cbn [concat]. rewrite app_nil_r. exact Hpn. }
  assert (HfrP : ~ In p (map fst P)).
  { intros Hq. apply Hfr. apply in_map_iff in Hq as (pn & E & Hq). apply in_map_iff. exists pn.
    split; [exact E | apply MB; exact Hq]. }
  assert (L0 : length l0 = length (r_calls R)) by (rewrite !length_app in C2; cbn [length] in C2; lia).
  assert (Ee : nth_error (r_calls R ++ [(fn, A)]) (length (r_calls R)) = Some (fn, A))
    by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
  assert (Ep : nth_error (l0 ++ [P]) (length (r_calls R)) = Some P)
    by (rewrite nth_error_app2, L0, Nat.sub_diag by lia; reflexivity).
  destruct (C4 _ _ _ Ee Ep) as [CE CL].
  assert (KR : forall x, A_G_REC <= x < A_G_REC + REC_SIZE ->
            ~ (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_NARGS <= x <
               A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_NARGS + 4) ->
            ~ (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_ARGS +
                 8 * Z.of_nat (length A) <= x <
               A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) + CALL_OFF_ARGS +
                 8 * Z.of_nat (length A) + 8) -> rd' x = rd x).
  { intros x H1 H2 H3. apply K; [left; exact H1 | exact H2 | exact H3]. }
  assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd' x = rd x).
  { intros x Hx'. apply K; [right; left; exact Hx' | |];
      unfold iv_apart, REC_SIZE, SC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia. }
  assert (KO : forall pn, In pn (oblk la ++ oblk lr) -> In pn bl' /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
  { intros pn Hpn. apply KQ. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    apply in_or_app. right. apply in_or_app. right. exact Hpn. }
  destruct (scn_rest_keep bl bl' rd rd' A_G_REC R la lr HA HP HX
              ltac:(intros x Hx'; apply KR;
                    unfold REC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia) KO)
    as (RA & RP & RX).
  unfold arep_at.
  refine (conj S1 (conj S2 (conj S3 (conj _ (conj RA (conj RP (conj RX _))))))).
  - unfold ag1_calls. cbn [set_calls r_calls r_spill l_calls l_spill].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ C6))))).
    + rewrite length_app in *. cbn [length] in *. lia.
    + rewrite !length_app in *. cbn [length] in *. lia.
    + replace (length (r_calls R ++ [(fn, A ++ [s])])) with (length (r_calls R ++ [(fn, A)]))
        by (rewrite !length_app; reflexivity).
      apply (scn_aval_keep rd); [exact C3 | intros x Hx'; apply KR;
        unfold REC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia].
    + intros i c P' Ec EP'.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      * assert (Ec0 : nth_error (r_calls R ++ [(fn, A)]) i = Some c)
          by (rewrite nth_error_app1 in Ec |- * by exact Hi; exact Ec).
        assert (EP0 : nth_error (l0 ++ [P]) i = Some P')
          by (rewrite nth_error_app1 in EP' |- * by lia; exact EP').
        destruct (C4 i c P' Ec0 EP0) as [Hc HL]. split; [|exact HL].
        apply (scn_call_keep bl bl' rd rd'); [exact Hc | |].
        -- intros x Hx'. apply KR;
             unfold REC_SIZE, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
        -- intros pn Hpn. apply KQ. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
           apply in_or_app. left. apply in_concat. exists P'. split; [eapply nth_error_In; exact EP0 | exact Hpn].
      * destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
        -- rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
           rewrite nth_error_app2, L0, Nat.sub_diag in EP' by lia. cbn in EP'. injection EP' as <-.
           split; [|apply Forall_app; split; [exact CL | constructor; [exact Hlx | constructor]]].
           apply (scn_call_arg bl bl' rd rd' _ fn A P s p k CE H6);
             [exact BN | exact BS | | | exact HfrP | exact Hp0 | exact Hin | exact Hsz | exact Hx].
           ++ intros a Ha H1 H2. apply KR; [unfold REC_SIZE, OFF_CALLS, CALL_SIZE in *; lia | exact H1 | exact H2].
           ++ intros pn Hpn. apply KQ. apply MB. exact Hpn.
        -- exfalso. assert (N : nth_error (r_calls R ++ [(fn, A ++ [s])]) i = None)
             by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
           rewrite N in Ec. discriminate.
    + apply (scn_call_keep bl bl' rd rd'); [exact C5 | |].
      * intros x Hx'. apply KS. unfold CALL_SIZE, SC_SIZE in *. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
        apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - pose proof (RecStep.lay_perm_lt l0 P ls la lr (p, k)) as PERM.
    unfold ag1_own. split.
    + apply (RecStep.nodup_fst_perm _ _ (Permutation_sym PERM)). apply RecStep.nodup_fst_snoc; [exact HND | exact Hfr].
    + intros pn Hpn. apply (Permutation_in _ PERM) in Hpn. apply in_app_or in Hpn as [Hpn|[<-|[]]];
        [exact (HAP pn Hpn)|]. cbn [fst snd]. split; assumption.
Qed.

(* (3) spill arm *)
Lemma scn_append_spill : forall bl bl' (rd rd' : reader) R fn A lc P la lr c s p k,
  arep_at bl rd A_G_REC A_REC_SPILL (rec_record R fn A) (RLay lc P la lr) ->
  length (r_calls R) = 16%nat ->
  c = A_REC_SPILL ->
  (length A < 6)%nat ->
  p <> 0 -> astr_atR rd' p s -> Z.of_nat (length s) <= LMAX -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 ->
  Forall (fun qk => iv_apart p k (fst qk) (snd qk)) bl ->
  iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
  aval_mem rd' (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
              exists pn, In pn bl /\ In pn (lay_blocks (RLay lc P la lr)) /\ fst pn <= a < fst pn + snd pn) ->
     ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
     ~ (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
     rd' a = rd a) ->
  (forall pn, In pn bl -> In pn bl') -> In (p, k) bl' ->
  arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R fn (A ++ [s])) (RLay lc (P ++ [(p, k)]) la lr).
Proof.
  intros bl bl' rd rd' R fn A lc P la lr c s p k HR Hn Hc H6 Hp0 Hx Hlx Hsz HF Ha1 Ha2 BN BS K Hbl Hin.
  subst c.
  rewrite (RecStep.rec_record_full R fn A Hn) in HR. rewrite (RecStep.rec_record_full R fn (A ++ [s]) Hn).
  assert (Hfr : ~ In p (map fst (lay_blocks (RLay lc P la lr))))
    by (apply (scn_fresh_not_lay bl rd _ _ _ _ p k HR); [lia | exact HF]).
  pose proof HR as (S1 & S2 & S3 & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  destruct HW as [HND HAP].
  cbn [set_spill r_calls r_spill r_answer r_reply l_calls l_spill l_answer l_reply fst snd]
    in C1, C2, C3, C4, C5, C6, HA, HP.
  assert (KQ : forall pn, In pn (lay_blocks (RLay lc P la lr)) ->
            In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
  { intros pn Hpn. destruct (scn_lay_facts _ _ _ _ _ _ pn HR Hpn) as (_ & _ & Hb).
    split; [exact (Hbl pn Hb)|]. intros i Hi. destruct (HAP pn Hpn) as [A1 A2].
    apply K; [right; right; exists pn; split; [exact Hb | split; [exact Hpn | lia]] | |];
      unfold iv_apart, SC_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia. }
  assert (MB : forall pn, In pn P -> In pn (lay_blocks (RLay lc P la lr))).
  { intros pn Hpn. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. apply in_or_app. right.
    apply in_or_app. left. exact Hpn. }
  assert (HfrP : ~ In p (map fst P)).
  { intros Hq. apply Hfr. apply in_map_iff in Hq as (pn & E & Hq). apply in_map_iff. exists pn.
    split; [exact E | apply MB; exact Hq]. }
  assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> rd' x = rd x).
  { intros x Hx'. apply K; [left; exact Hx' | |];
      unfold iv_apart, REC_SIZE, SC_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia. }
  assert (KO : forall pn, In pn (oblk la ++ oblk lr) -> In pn bl' /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
  { intros pn Hpn. apply KQ. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
    apply in_or_app. right. apply in_or_app. right. exact Hpn. }
  destruct (scn_rest_keep bl bl' rd rd' A_G_REC R la lr HA HP HX
              ltac:(intros x Hx'; apply KG; unfold REC_SIZE; lia) KO)
    as (RA & RP & RX).
  unfold arep_at.
  refine (conj S1 (conj S2 (conj S3 (conj _ (conj RA (conj RP (conj RX _))))))).
  - unfold ag1_calls. cbn [set_spill r_calls r_spill l_calls l_spill fst snd].
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ _))))).
    + apply (scn_aval_keep rd); [exact C3 | intros x Hx'; apply KG; unfold OFF_NCALLS, REC_SIZE in *; lia].
    + intros i c P' Ec EP'. destruct (C4 i c P' Ec EP') as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (scn_call_keep bl bl' rd rd'); [exact Hc | |].
      * intros x Hx'. apply KG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
        apply in_or_app. left. apply in_concat. exists P'. split; [eapply nth_error_In; exact EP' | exact Hpn].
    + apply (scn_call_arg bl bl' rd rd' A_REC_SPILL fn A P s p k C5 H6);
        [exact BN | exact BS | | | exact HfrP | exact Hp0 | exact Hin | exact Hsz | exact Hx].
      * intros a Ha H1 H2. apply K; [right; left; unfold CALL_SIZE, SC_SIZE in *; lia | exact H1 | exact H2].
      * intros pn Hpn. apply KQ. apply MB. exact Hpn.
    + apply Forall_app. split; [exact C6 | constructor; [exact Hlx | constructor]].
  - pose proof (RecStep.lay_perm_full lc P la lr (p, k)) as PERM.
    unfold ag1_own. split.
    + apply (RecStep.nodup_fst_perm _ _ (Permutation_sym PERM)). apply RecStep.nodup_fst_snoc; [exact HND | exact Hfr].
    + intros pn Hpn. apply (Permutation_in _ PERM) in Hpn. apply in_app_or in Hpn as [Hpn|[<-|[]]];
        [exact (HAP pn Hpn)|]. cbn [fst snd]. split; assumption.
Qed.

(* (3) either slot, over the recorder's block list O instead of a layout (the rec_repA form of CmdRep.v:154-155
   for any block list) *)
Lemma scn_append : forall bl bl' (rd rd' : reader) R fn A O c s p k,
  (exists Q, arep_at bl rd A_G_REC A_REC_SPILL (rec_record R fn A) Q /\ (forall pn, In pn O <-> In pn (lay_blocks Q))) ->
  ((length (r_calls R) < 16)%nat /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) \/
   (16 <= length (r_calls R))%nat /\ c = A_REC_SPILL) ->
  (length A < 6)%nat ->
  p <> 0 -> astr_atR rd' p s -> Z.of_nat (length s) <= LMAX -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 ->
  Forall (fun qk => iv_apart p k (fst qk) (snd qk)) bl ->
  iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
  aval_mem rd' (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
              exists pn, In pn bl /\ In pn O /\ fst pn <= a < fst pn + snd pn) ->
     ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
     ~ (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
     rd' a = rd a) ->
  (forall pn, In pn bl -> In pn bl') -> In (p, k) bl' ->
  exists Q', arep_at bl' rd' A_G_REC A_REC_SPILL (rec_record R fn (A ++ [s])) Q' /\
    (forall pn, In pn ((p, k) :: O) <-> In pn (lay_blocks Q')).
Proof.
  intros bl bl' rd rd' R fn A O c s p k (Q & HR & HO) Hslot H6 Hp0 Hx Hlx Hsz HF Ha1 Ha2 BN BS K Hbl Hin.
  assert (K' : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
              exists pn, In pn bl /\ In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn) ->
     ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
     ~ (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
     rd' a = rd a).
  { intros a Ha H1 H2. apply K; [|exact H1 | exact H2].
    destruct Ha as [Ha|[Ha|(pn & Hb & Hq & Ha)]]; [left; exact Ha | right; left; exact Ha |].
    right; right. exists pn. split; [exact Hb|]. split; [apply HO; exact Hq | exact Ha]. }
  assert (HOc : forall l', Permutation l' (lay_blocks Q ++ [(p, k)]) ->
            forall pn, In pn ((p, k) :: O) <-> In pn l').
  { intros l' HP pn. pose proof (RecStep.lay_perm_iff O _ _ (p, k) HO HP pn) as E.
    split; intros H.
    - apply E. apply in_or_app. destruct H as [H|H]; [right; left; exact H | left; exact H].
    - apply E in H. apply in_app_or in H as [H|[H|[]]]; [right; exact H | left; exact H]. }
  destruct Q as [lc ls la lr].
  destruct Hslot as [[Hn Hc]|[Hn Hc]].
  - pose proof HR as (_ & _ & _ & (_ & C2 & _) & _).
    rewrite (RecStep.rec_record_lt R fn A Hn) in C2.
    cbn [set_calls r_calls l_calls] in C2. rewrite length_app in C2. cbn [length] in C2.
    assert (NE : lc <> []) by (intros E; rewrite E in C2; cbn in C2; lia).
    destruct (exists_last NE) as (l0 & P & E). subst lc.
    exists (RLay (l0 ++ [P ++ [(p, k)]]) ls la lr). split.
    + exact (scn_append_call bl bl' rd rd' R fn A l0 P ls la lr c s p k
               HR Hn Hc H6 Hp0 Hx Hlx Hsz HF Ha1 Ha2 BN BS K' Hbl Hin).
    + exact (HOc _ (RecStep.lay_perm_lt l0 P ls la lr (p, k))).
  - assert (Hn16 : length (r_calls R) = 16%nat).
    { pose proof HR as (_ & _ & _ & (C1 & _) & _).
      assert (Hf : Nat.ltb (length (r_calls R)) 16 = false) by (apply Nat.ltb_ge; exact Hn).
      unfold rec_record in C1. rewrite Hf in C1. cbn [set_spill r_calls] in C1. lia. }
    exists (RLay lc (ls ++ [(p, k)]) la lr). split.
    + exact (scn_append_spill bl bl' rd rd' R fn A lc ls la lr c s p k
               HR Hn16 Hc H6 Hp0 Hx Hlx Hsz HF Ha1 Ha2 BN BS K' Hbl Hin).
    + exact (HOc _ (RecStep.lay_perm_full lc ls la lr (p, k))).
Qed.

Section e.
Variable B : asyms.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The same three steps over CmdRep.v's rec_repA, the form a walk holds *)

Lemma scn_record_lt_rep : forall ly S (rd rd' : reader) R O n c fn,
  rec_repA B ly S rd R O ->
  length (r_calls R) = n -> (n < 16)%nat -> 0 <= fn < REC_FN_COUNT ->
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat n + 1) ->
  aval_mem rd' (c + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 0 ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
              exists pn, In pn (ablocks B ly S) /\ In pn O /\ fst pn <= a < fst pn + snd pn) ->
     ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + CALL_SIZE) -> rd' a = rd a) ->
  rec_repA B ly S rd' (rec_record R fn []) O.
Proof.
  intros ly S rd rd' R O n c fn (Q & HR & HO) Hn Hlt Hfn Hc BN BF BA K.
  exists (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)). split.
  - apply (scn_record_lt _ rd rd' R Q n c fn HR Hn Hlt Hfn Hc BN BF BA).
    intros a Ha H1 H2. apply K; [|exact H1 | exact H2].
    destruct Ha as [Ha|[Ha|(pn & Hb & Hq & Ha)]]; [left; exact Ha | right; left; exact Ha |].
    right; right. exists pn. split; [exact Hb|]. split; [apply HO; exact Hq | exact Ha].
  - rewrite scn_lay_lt. exact HO.
Qed.

Lemma scn_record_full_rep : forall ly S (rd rd' : reader) R O fn,
  rec_repA B ly S rd R O ->
  length (r_calls R) = 16%nat -> snd (r_spill R) = [] -> 0 <= fn < REC_FN_COUNT ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 fn ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
              exists pn, In pn (ablocks B ly S) /\ In pn O /\ fst pn <= a < fst pn + snd pn) ->
     ~ (A_REC_SPILL <= a < A_REC_SPILL + CALL_SIZE) -> rd' a = rd a) ->
  rec_repA B ly S rd' (rec_record R fn []) O.
Proof.
  intros ly S rd rd' R O fn (Q & HR & HO) Hn Hsp Hfn BF BA K.
  exists Q. split; [|exact HO].
  apply (scn_record_full _ rd rd' R Q fn HR Hn Hsp Hfn BF BA).
  intros a Ha H1. apply K; [|exact H1].
  destruct Ha as [Ha|[Ha|(pn & Hb & Hq & Ha)]]; [left; exact Ha | right; left; exact Ha |].
  right; right. exists pn. split; [exact Hb|]. split; [apply HO; exact Hq | exact Ha].
Qed.

Lemma scn_append_rep : forall ly S ly' S' (rd rd' : reader) R fn A O c s p k,
  rec_repA B ly S rd (rec_record R fn A) O ->
  ((length (r_calls R) < 16)%nat /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) \/
   (16 <= length (r_calls R))%nat /\ c = A_REC_SPILL) ->
  (length A < 6)%nat ->
  p <> 0 -> astr_atR rd' p s -> Z.of_nat (length s) <= LMAX -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 ->
  Forall (fun qk => iv_apart p k (fst qk) (snd qk)) (ablocks B ly S) ->
  iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
  aval_mem rd' (c + CALL_OFF_NARGS) 4 (Z.of_nat (length A) + 1) ->
  aval_mem rd' (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A)) 8 p ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
              exists pn, In pn (ablocks B ly S) /\ In pn O /\ fst pn <= a < fst pn + snd pn) ->
     ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
     ~ (c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) <= a < c + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8) ->
     rd' a = rd a) ->
  Permutation (ablocks B ly' S') ((p, k) :: ablocks B ly S) ->
  rec_repA B ly' S' rd' (rec_record R fn (A ++ [s])) ((p, k) :: O).
Proof.
  intros ly S ly' S' rd rd' R fn A O c s p k HR Hslot H6 Hp0 Hx Hlx Hsz HF Ha1 Ha2 BN BS K HPm.
  exact (scn_append (ablocks B ly S) (ablocks B ly' S') rd rd' R fn A O c s p k HR Hslot H6 Hp0 Hx Hlx Hsz HF
           Ha1 Ha2 BN BS K
           (fun pn H => Permutation_in _ (Permutation_sym HPm) (or_intror H))
           (Permutation_in _ (Permutation_sym HPm) (or_introl eq_refl))).
Qed.
End e.
End f.
End d.
