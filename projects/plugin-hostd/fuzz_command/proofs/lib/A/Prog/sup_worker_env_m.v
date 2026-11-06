(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder's model steps that sup_worker_env's ASan walk takes over
   rec_repA (lib/A/Prog/CmdRep.v): record() (recorder.c:205-221) on the slot arm and on the spill arm, and
   arg_s (recorder.c:223-227) adding one argument; the transports aval_mem_kept .. rec_repA_kept are copied from
   answer_code's walk in an earlier version of lib/A/Prog/answer_code.v (:230-341). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the slot record() picks: g_rec.calls[n] while the table has room, else record.spill *)
Definition swe_slot_of (n : Z) : Z := if n <? 16 then A_G_REC + OFF_CALLS + CALL_SIZE * n else A_REC_SPILL.
(* the bytes of g_rec and of record.spill *)
Definition in_recg (a : Z) : Prop := (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).

Section d.
Variable B : asyms.

(* ---------- the recorder's state survives writes outside g_rec, record.spill and its own blocks ---------- *)
Lemma aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma acall_at_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn. unfold lay_blocks in Hpn.
destruct HA as (_ & _ & _ & (Hc1 & Hc2 & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
+ destruct (Hc4 i c P Hc Hi) as ((_ & _ & HL & _ & _ & _ & H7) & _).
apply In_nth_error in Hin as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs.
* exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
* exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
+ exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- destruct Hsp as (_ & _ & HL & _ & _ & _ & H7). apply In_nth_error in Hpn as (k & Hk).
destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs.
+ exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
+ exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) k) ltac:(rewrite Hk; discriminate)). lia.
- unfold aanswer_at in Ha. destruct (r_answer R), (l_answer Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 Ha))).
- unfold areply_at in Hr. destruct (r_reply R), (l_reply Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hr))))).
Qed.
Lemma rec_repA_kept : forall ly S rd ly' S' rd' R O, rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + 56 -> rd' a = rd a) ->
(forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S rd ly' S' rd' R O (Q & HA & HO) Hbl Hg Hs Hb. exists Q. split; [|exact HO].
assert (HblQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S')) by (intros pn Hpn; apply Hbl, HO, Hpn).
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros [p n] i Hpn Hi; apply (Hb p n i (proj2 (HO (p, n)) Hpn) Hi)).
unfold lay_blocks in HblQ, HbQ.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & Hown).
unfold arep_at, ag1_calls, ag1_scalars, aanswer_at, areply_at in *.
unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, CALL_SIZE in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ split; [exact C1|]. split; [exact C2|].
split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk; apply Hg; lia]|].
split.
- intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
pose proof HC as (_ & HL6 & _).
apply (acall_at_kept (ablocks B ly S) _ rd); [exact HC | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
+ intros j Hj. rewrite <- !Z.add_assoc. apply Hg. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
- split; [|exact C6].
pose proof C5 as (_ & HL6 & _).
apply (acall_at_kept (ablocks B ly S) _ rd); [exact C5 | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
+ intros j Hj. apply Hs. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hpn. }
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
- destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (Some q) ++ oblk (l_reply Q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A6].
- apply (aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
- destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (Some q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
split; [apply (rabytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A8].
- destruct Hr as [A1 A2]. split; apply (aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [|exact Hown].
split; [apply (aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.

(* ---------- helpers of the three model steps below ---------- *)
Local Ltac swe_m_lia :=
  unfold in_recg, REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE, CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *; lia.

Lemma swe_m_spill_off : A_REC_SPILL = A_G_REC + 1184.
Proof. reflexivity. Qed.

Lemma swe_m_slot_lt : forall n, (n < 16)%nat -> swe_slot_of (Z.of_nat n) = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n.
Proof. intros n Hn. unfold swe_slot_of. destruct (Z.ltb_spec (Z.of_nat n) 16); [reflexivity | lia]. Qed.

Lemma swe_m_slot_16 : swe_slot_of (Z.of_nat 16%nat) = A_REC_SPILL.
Proof. reflexivity. Qed.

Lemma swe_m_call_empty : forall bl (rd : reader) a fn, 0 <= fn < REC_FN_COUNT ->
aval_mem rd a 4 fn -> aval_mem rd (a + 4) 4 0 -> acall_at bl rd a (fn, []) [].
Proof.
intros bl rd a fn Hfn H1 H2. unfold acall_at, CALL_OFF_FN, CALL_OFF_NARGS. cbn [fst snd length].
split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
split; [rewrite Z.add_0_r; exact H1|]. split; [exact H2|]. split; [constructor|].
intros k s pn Hs. destruct k; cbn in Hs; discriminate.
Qed.

Lemma swe_m_call_arg : forall bl (rd rd' : reader) a fn A x P p,
acall_at bl rd a (fn, A) P -> (length A < 6)%nat ->
In (p, Z.of_nat (length x) + 1) bl -> p <> 0 -> ~ In p (map fst P) -> Z.of_nat (length x) <= LMAX ->
astr_atR rd' p x ->
aval_mem rd' (a + 4) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (a + 8 + 8 * Z.of_nat (length A)) 8 p ->
(forall i, (0 <= i < 4 \/ 8 <= i < 8 + 8 * Z.of_nat (length A)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl rd' a (fn, A ++ [x]) (P ++ [(p, Z.of_nat (length x) + 1)]).
Proof.
intros bl rd rd' a fn A x P p (H1 & H2 & H3 & H4 & H5 & H6 & H7) HA6 Hpin Hp0 HpP Hlx Hstr Hna Harg Hk Hb.
unfold acall_at, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *. cbn [fst snd] in *.
split; [exact H1|].
split; [rewrite length_app; cbn [length]; lia|].
split; [rewrite !length_app; cbn [length]; lia|].
split; [apply (aval_mem_kept rd); [exact H4 | intros k Hk'; rewrite <- Z.add_assoc; apply Hk; lia]|].
split; [rewrite length_app, Nat2Z.inj_add; exact Hna|].
split.
{ rewrite map_app. cbn [map fst]. apply NoDup_ListNoDup. apply NoDup_ListNoDup in H6.
  eapply Permutation_NoDup; [apply Permutation_cons_append | constructor; [exact HpP | exact H6]]. }
intros k s pn Hs Hpn.
destruct (Nat.lt_ge_cases k (length A)) as [Hk1|Hk1].
- rewrite nth_error_app1 in Hs by exact Hk1. rewrite nth_error_app1 in Hpn by lia.
  destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
  split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Hk; lia]|].
  split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hb; [exact (nth_error_In _ _ Hpn) | lia]].
- destruct (Nat.eq_dec k (length A)) as [->|Hne].
  + rewrite nth_error_app2, Nat.sub_diag in Hs by lia. cbn in Hs. injection Hs as <-.
    rewrite nth_error_app2 in Hpn by lia. rewrite H3, Nat.sub_diag in Hpn. cbn in Hpn. injection Hpn as <-.
    cbn [fst snd]. split; [exact Harg|]. split; [exact Hp0|]. split; [exact Hpin|]. split; [lia | exact Hstr].
  + exfalso. assert (E : nth_error (A ++ [x]) k = None) by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
    congruence.
Qed.

Lemma swe_m_blk_pos : forall bl rd gr sc R Q, arep_at bl rd gr sc R Q -> forall pn, In pn (lay_blocks Q) -> 1 <= snd pn.
Proof.
intros bl rd gr sc R Q HA pn Hpn. unfold lay_blocks in Hpn.
destruct HA as (_ & _ & _ & (Hc1 & Hc2 & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
  + destruct (Hc4 i c P Hc Hi) as ((_ & _ & HL & _ & _ & _ & H7) & _).
    apply In_nth_error in Hin as (k & Hk).
    destruct (nth_error (snd c) k) as [s|] eqn:Hs.
    * destruct (H7 k s pn Hs Hk) as (_ & _ & _ & HB & _). lia.
    * exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
  + exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- destruct Hsp as (_ & _ & HL & _ & _ & _ & H7). apply In_nth_error in Hpn as (k & Hk).
  destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs.
  + destruct (H7 k s pn Hs Hk) as (_ & _ & _ & HB & _). lia.
  + exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) k) ltac:(rewrite Hk; discriminate)). lia.
- unfold aanswer_at in Ha. destruct (r_answer R) as [y|], (l_answer Q) as [q|]; cbn in Hpn; try contradiction.
  destruct Hpn as [<- | []]. destruct Ha as (_ & _ & _ & HB & _). lia.
- unfold areply_at in Hr. destruct (r_reply R) as [y|], (l_reply Q) as [q|]; cbn in Hpn; try contradiction.
  destruct Hpn as [<- | []]. destruct Hr as (_ & _ & _ & HX & _ & HB & _).
  destruct y as [|b y]; [exfalso; apply HX; reflexivity | cbn [length] in HB; lia].
Qed.

Lemma swe_m_tail_kept : forall bl (rd rd' : reader) gr R Q,
aanswer_at bl rd gr (r_answer R) (l_answer Q) -> areply_at bl rd gr (r_reply R) (l_reply Q) -> ag1_scalars rd gr R ->
(forall a, (gr <= a < gr + 8 \/ gr + 912 <= a < gr + 960) -> rd' a = rd a) ->
(forall pn i, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aanswer_at bl rd' gr (r_answer R) (l_answer Q) /\ areply_at bl rd' gr (r_reply R) (l_reply Q) /\ ag1_scalars rd' gr R.
Proof.
intros bl rd rd' gr R Q Ha Hr (S1 & S2 & S3 & S4 & S5 & S6) Hg HbQ.
unfold ag1_scalars, aanswer_at, areply_at in *.
unfold OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
- destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
  split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
  split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply HbQ; [apply in_app_iff; left; left; reflexivity | lia]] | exact A6].
- apply (aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
- destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
  split; [apply (aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
  split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
  split; [apply (rabytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [apply in_app_iff; right; left; reflexivity | lia]] | exact A8].
- destruct Hr as [A1 A2]. split; apply (aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [apply (aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.

Lemma swe_m_perm_core : forall (a : Z * Z) l m, Permutation (a :: l ++ m) ((l ++ [a]) ++ m).
Proof. intros a l m. rewrite <- app_assoc. cbn [app]. apply Permutation_middle. Qed.

Lemma swe_m_lay_slot : forall Q L0 P (a : Z * Z), l_calls Q = L0 ++ [P] ->
Permutation (a :: lay_blocks Q) (lay_blocks (RLay (L0 ++ [P ++ [a]]) (l_spill Q) (l_answer Q) (l_reply Q))).
Proof.
intros Q L0 P a HL. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
rewrite HL, !concat_app. cbn [concat]. rewrite !app_nil_r.
rewrite (app_assoc (concat L0) P [a]). apply swe_m_perm_core.
Qed.

Lemma swe_m_lay_spill : forall Q (a : Z * Z),
Permutation (a :: lay_blocks Q) (lay_blocks (RLay (l_calls Q) (l_spill Q ++ [a]) (l_answer Q) (l_reply Q))).
Proof.
intros Q a. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply].
rewrite (app_assoc (concat (l_calls Q)) (l_spill Q)), (app_assoc (concat (l_calls Q)) (l_spill Q ++ [a])),
  (app_assoc (concat (l_calls Q)) (l_spill Q) [a]).
apply swe_m_perm_core.
Qed.

Lemma swe_m_iff_perm : forall (O L L' : list (Z * Z)) a, (forall pn, In pn O <-> In pn L) -> Permutation (a :: L) L' ->
forall pn, In pn (O ++ [a]) <-> In pn L'.
Proof.
intros O L L' a HO Hp pn. split; intros H.
- eapply Permutation_in; [exact Hp|]. apply in_app_iff in H as [H | [H | []]].
  + right. apply HO. exact H.
  + left. exact H.
- assert (H' : In pn (a :: L)) by (eapply Permutation_in; [apply Permutation_sym; exact Hp | exact H]).
  apply in_app_iff. destruct H' as [H' | H'].
  + right. left. exact H'.
  + left. apply HO. exact H'.
Qed.

Lemma swe_m_own_perm : forall gr sc Q Q' (a : Z * Z), ag1_own gr sc Q -> Permutation (a :: lay_blocks Q) (lay_blocks Q') ->
~ In (fst a) (map fst (lay_blocks Q)) -> iv_apart (fst a) (snd a) gr REC_SIZE -> iv_apart (fst a) (snd a) sc SC_SIZE ->
ag1_own gr sc Q'.
Proof.
intros gr sc Q Q' a [Hnd Hiv] Hp Ha Hg Hs. split.
- apply NoDup_ListNoDup. apply NoDup_ListNoDup in Hnd.
  eapply Permutation_NoDup; [apply Permutation_map; exact Hp | cbn [map]; constructor; [exact Ha | exact Hnd]].
- intros q Hq. assert (H' : In q (a :: lay_blocks Q)) by (eapply Permutation_in; [apply Permutation_sym; exact Hp | exact Hq]).
  destruct H' as [<- | H']; [exact (conj Hg Hs) | exact (Hiv q H')].
Qed.

(* ---------- record(): the slot arm (recorder.c:216-219): ncalls := n + 1, then the slot's fn and nargs ---------- *)
Lemma swe_rec_slot : forall ly S (rd rd' : reader) R O,
rec_repA B ly S rd R O ->
(length (r_calls R) < 16)%nat ->
aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
aval_mem rd' (swe_slot_of (Z.of_nat (length (r_calls R)))) 4 REC_WORKER_ENV ->
aval_mem rd' (swe_slot_of (Z.of_nat (length (r_calls R))) + 4) 4 0 ->
(forall a, in_recg a -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
  ~ (swe_slot_of (Z.of_nat (length (r_calls R))) <= a < swe_slot_of (Z.of_nat (length (r_calls R))) + 8) ->
  rd' a = rd a) ->
(forall p k i, In (p, k) O -> 0 <= i < k -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly S rd' (rec_record R REC_WORKER_ENV []) O.
Proof.
intros ly S rd rd' R O H Hn Hnc Hfn Hna Hk Hb.
pose proof (rec_repA_in ly S rd R O H) as Hbl0.
pose proof swe_m_spill_off as Hso.
rewrite (swe_m_slot_lt _ Hn) in Hfn, Hna, Hk.
rewrite (rec_record_calls R REC_WORKER_ENV [] Hn).
destruct H as (Q & HA & HO).
assert (HblQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly S)) by (intros pn Hpn; apply Hbl0, HO, Hpn).
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros [q k] i Hpn Hi; exact (Hb q k i (proj2 (HO (q, k)) Hpn) Hi)).
unfold lay_blocks in HblQ, HbQ.
assert (Hlay : lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q)
by (unfold lay_blocks; cbn [l_calls l_spill l_answer l_reply]; rewrite concat_app; cbn [concat app]; rewrite app_nil_r; reflexivity).
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HS & Hown).
assert (Hg : forall a, (A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + 912 <= a < A_G_REC + 960) -> rd' a = rd a)
by (intros a Ha'; apply Hk; swe_m_lia).
assert (Ht : forall pn i, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros pn i Hpn Hi; apply HbQ; [apply in_app_iff; right; apply in_app_iff; right; exact Hpn | exact Hi]).
destruct (swe_m_tail_kept _ rd rd' A_G_REC R Q Ha Hr HS Hg Ht) as (T1 & T2 & T3).
exists (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)).
split; [|rewrite Hlay; exact HO].
unfold arep_at. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ unfold ag1_calls, set_calls. cbn [r_calls r_spill l_calls l_spill].
  rewrite !length_app. cbn [length].
  split; [lia|]. split; [lia|].
  split; [rewrite Nat2Z.inj_add; exact Hnc|].
  split.
  - intros i c P Hc HP.
    destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
    + rewrite nth_error_app1 in Hc by exact Hi. rewrite nth_error_app1 in HP by lia.
      destruct (C4 i c P Hc HP) as [HC HF]. split; [|exact HF].
      pose proof HC as (_ & HL6 & _).
      apply (acall_at_kept (ablocks B ly S) _ rd); [exact HC | | |].
      * intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ HP) | exact Hpn].
      * intros j Hj. apply Hk; swe_m_lia.
      * intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ HP) | exact Hpn].
    + destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
      * rewrite nth_error_app2, Nat.sub_diag in Hc by lia. cbn in Hc. injection Hc as <-.
        rewrite nth_error_app2 in HP by lia. rewrite C2, Nat.sub_diag in HP. cbn in HP. injection HP as <-.
        split; [|cbn [snd]; constructor].
        apply swe_m_call_empty; [unfold REC_WORKER_ENV, REC_FN_COUNT; lia | exact Hfn | exact Hna].
      * exfalso. assert (E : nth_error (r_calls R ++ [(REC_WORKER_ENV, [])]) i = None)
        by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
        congruence.
  - split; [|exact C6].
    pose proof C5 as (_ & HL6 & _).
    apply (acall_at_kept (ablocks B ly S) _ rd); [exact C5 | | |].
    + intros pn Hpn. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
    + intros j Hj. apply Hk; swe_m_lia.
    + intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hpn. }
split; [exact T1|]. split; [exact T2|]. split; [exact T3|].
unfold ag1_own. rewrite Hlay. exact Hown.
Qed.

(* ---------- record(): the spill arm (recorder.c:210-215), after rec_calls_free emptied record.spill ---------- *)
Lemma swe_rec_spill : forall ly S (rd rd' : reader) R O,
rec_repA B ly S rd R O -> snd (r_spill R) = [] ->
aval_mem rd' A_REC_SPILL 4 REC_WORKER_ENV -> aval_mem rd' (A_REC_SPILL + 4) 4 0 ->
(forall a, in_recg a -> ~ (A_REC_SPILL <= a < A_REC_SPILL + 8) -> rd' a = rd a) ->
(forall p k i, In (p, k) O -> 0 <= i < k -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly S rd' (set_spill R (REC_WORKER_ENV, [])) O.
Proof.
intros ly S rd rd' R O H Hsn Hfn Hna Hk Hb.
pose proof (rec_repA_in ly S rd R O H) as Hbl0.
pose proof swe_m_spill_off as Hso.
destruct H as (Q & HA & HO).
assert (HblQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly S)) by (intros pn Hpn; apply Hbl0, HO, Hpn).
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros [q k] i Hpn Hi; exact (Hb q k i (proj2 (HO (q, k)) Hpn) Hi)).
unfold lay_blocks in HblQ, HbQ.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HS & Hown).
assert (Hsp : l_spill Q = []) by (destruct C5 as (_ & _ & HL & _); apply length_zero_iff_nil; rewrite HL, Hsn; reflexivity).
assert (Hg : forall a, (A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + 912 <= a < A_G_REC + 960) -> rd' a = rd a)
by (intros a Ha'; apply Hk; swe_m_lia).
assert (Ht : forall pn i, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros pn i Hpn Hi; apply HbQ; [apply in_app_iff; right; apply in_app_iff; right; exact Hpn | exact Hi]).
destruct (swe_m_tail_kept _ rd rd' A_G_REC R Q Ha Hr HS Hg Ht) as (T1 & T2 & T3).
exists Q. split; [|exact HO].
unfold arep_at. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ unfold ag1_calls, set_spill. cbn [r_calls r_spill].
  split; [exact C1|]. split; [exact C2|].
  split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk'; apply Hk; swe_m_lia]|].
  split.
  - intros i c P Hc HP. destruct (C4 i c P Hc HP) as [HC HF]. split; [|exact HF].
    pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
    pose proof HC as (_ & HL6 & _).
    apply (acall_at_kept (ablocks B ly S) _ rd); [exact HC | | |].
    + intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ HP) | exact Hpn].
    + intros j Hj. apply Hk; swe_m_lia.
    + intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ HP) | exact Hpn].
  - split; [rewrite Hsp; apply swe_m_call_empty; [unfold REC_WORKER_ENV, REC_FN_COUNT; lia | exact Hfn | exact Hna]|].
    cbn [snd]. constructor. }
split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. exact Hown.
Qed.

(* ---------- arg_s (recorder.c:223-227): nargs := m + 1, args[m] := a fresh copy of x ---------- *)
Lemma swe_rec_arg : forall ly S (rd rd' : reader) R O (A : list (list byte)) (x : list byte) (p : Z),
rec_repA B ly S rd (rec_record R REC_WORKER_ENV A) O ->
(length (r_calls R) <= 16)%nat -> (length A < 6)%nat ->
In (p, Z.of_nat (length x) + 1) (ablocks B ly S) -> p <> 0 ->
Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O ->
iv_apart p (Z.of_nat (length x) + 1) A_G_REC REC_SIZE ->
iv_apart p (Z.of_nat (length x) + 1) A_REC_SPILL SC_SIZE ->
Z.of_nat (length x) <= LMAX ->
astr_atR rd' p x ->
aval_mem rd' (swe_slot_of (Z.of_nat (length (r_calls R))) + 4) 4 (Z.of_nat (length A) + 1) ->
aval_mem rd' (swe_slot_of (Z.of_nat (length (r_calls R))) + 8 + 8 * Z.of_nat (length A)) 8 p ->
(forall a, in_recg a ->
  ~ (swe_slot_of (Z.of_nat (length (r_calls R))) + 4 <= a < swe_slot_of (Z.of_nat (length (r_calls R))) + 8) ->
  ~ (swe_slot_of (Z.of_nat (length (r_calls R))) + 8 + 8 * Z.of_nat (length A) <= a <
     swe_slot_of (Z.of_nat (length (r_calls R))) + 16 + 8 * Z.of_nat (length A)) ->
  rd' a = rd a) ->
(forall q k i, In (q, k) O -> 0 <= i < k -> rd' (q + i) = rd (q + i)) ->
rec_repA B ly S rd' (rec_record R REC_WORKER_ENV (A ++ [x])) (O ++ [(p, Z.of_nat (length x) + 1)]).
Proof.
intros ly S rd rd' R O A x p H Hn16 HA6 Hpin Hp0 Hap Hapg Haps Hlx Hstr Hnargs Harg Hk Hb.
pose proof (rec_repA_in ly S rd _ O H) as Hbl0.
pose proof swe_m_spill_off as Hso.
assert (HpO : forall q k, In (q, k) O -> q <> p).
{ intros q k Hq E. subst q.
  assert (Hk1 : 1 <= k).
  { destruct H as (Q & HA & HO). exact (swe_m_blk_pos _ _ _ _ _ _ HA (p, k) (proj1 (HO (p, k)) Hq)). }
  pose proof (proj1 (Forall_forall _ _) Hap (p, k) Hq) as H2. unfold iv_apart in H2. cbn [fst snd] in H2. lia. }
destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt|Hge].
- (* the slot arm: the call is g_rec.calls[n] *)
  rewrite (rec_record_calls R REC_WORKER_ENV A Hlt) in H.
  rewrite (rec_record_calls R REC_WORKER_ENV (A ++ [x]) Hlt).
  rewrite (swe_m_slot_lt _ Hlt) in Hnargs, Harg, Hk.
  destruct H as (Q & HA & HO).
  assert (HblQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly S)) by (intros pn Hpn; apply Hbl0, HO, Hpn).
  assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
  by (intros [q k] i Hpn Hi; exact (Hb q k i (proj2 (HO (q, k)) Hpn) Hi)).
  assert (HpQ : ~ In p (map fst (lay_blocks Q))).
  { intros Hin. apply in_map_iff in Hin as ([q k] & E & Hin). cbn [fst] in E. exact (HpO q k (proj2 (HO (q, k)) Hin) E). }
  unfold lay_blocks in HblQ, HbQ.
  destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HS & Hown).
  unfold set_calls in C1, C2, C3, C4, C5, C6. cbn [r_calls r_spill] in C1, C2, C3, C4, C5, C6.
  rewrite length_app in C1, C2, C3. cbn [length] in C1, C2, C3.
  assert (HLne : l_calls Q <> []) by (intro E; rewrite E in C2; cbn [length] in C2; lia).
  destruct (@exists_last _ (l_calls Q) HLne) as (L0 & P & HL).
  assert (HL0 : length L0 = length (r_calls R)) by (rewrite HL, length_app in C2; cbn [length] in C2; lia).
  assert (E1 : nth_error (r_calls R ++ [(REC_WORKER_ENV, A)]) (length (r_calls R)) = Some (REC_WORKER_ENV, A))
  by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
  assert (E2 : nth_error (l_calls Q) (length (r_calls R)) = Some P)
  by (rewrite HL, nth_error_app2 by lia; rewrite HL0, Nat.sub_diag; reflexivity).
  destruct (C4 _ _ _ E1 E2) as [HC HF].
  assert (HPin : forall pn, In pn P -> In pn (concat (l_calls Q))).
  { intros pn Hpn. apply in_concat. exists P. split; [rewrite HL; apply in_app_iff; right; left; reflexivity | exact Hpn]. }
  pose proof (swe_m_lay_slot Q L0 P (p, Z.of_nat (length x) + 1) HL) as Hperm.
  assert (Hg : forall a, (A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + 912 <= a < A_G_REC + 960) -> rd' a = rd a)
  by (intros a Ha'; apply Hk; swe_m_lia).
  assert (Ht : forall pn i, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
  by (intros pn i Hpn Hi; apply HbQ; [apply in_app_iff; right; apply in_app_iff; right; exact Hpn | exact Hi]).
  destruct (swe_m_tail_kept _ rd rd' A_G_REC R Q Ha Hr HS Hg Ht) as (T1 & T2 & T3).
  exists (RLay (L0 ++ [P ++ [(p, Z.of_nat (length x) + 1)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
  split; [|exact (swe_m_iff_perm _ _ _ _ HO Hperm)].
  unfold arep_at. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  split.
  { unfold ag1_calls, set_calls. cbn [r_calls r_spill l_calls l_spill].
    rewrite !length_app. cbn [length].
    split; [lia|]. split; [lia|].
    split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk'; apply Hk; swe_m_lia]|].
    split.
    - intros i c P' Hc HP'.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      + rewrite nth_error_app1 in Hc by exact Hi. rewrite nth_error_app1 in HP' by lia.
        assert (Hc0 : nth_error (r_calls R ++ [(REC_WORKER_ENV, A)]) i = Some c) by (rewrite nth_error_app1 by exact Hi; exact Hc).
        assert (HP0 : nth_error (l_calls Q) i = Some P') by (rewrite HL, nth_error_app1 by lia; exact HP').
        destruct (C4 i c P' Hc0 HP0) as [HC' HF']. split; [|exact HF'].
        pose proof HC' as (_ & HL6 & _).
        apply (acall_at_kept (ablocks B ly S) _ rd); [exact HC' | | |].
        * intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P'. split; [exact (nth_error_In _ _ HP0) | exact Hpn].
        * intros j Hj. apply Hk; swe_m_lia.
        * intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P'. split; [exact (nth_error_In _ _ HP0) | exact Hpn].
      + destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
        * rewrite nth_error_app2, Nat.sub_diag in Hc by lia. cbn in Hc. injection Hc as <-.
          rewrite nth_error_app2 in HP' by lia. rewrite HL0, Nat.sub_diag in HP'. cbn in HP'. injection HP' as <-.
          split.
          { apply (swe_m_call_arg _ rd); [exact HC | exact HA6 | exact Hpin | exact Hp0 | | exact Hlx | exact Hstr | exact Hnargs | exact Harg | | ].
            - intros Hin. apply HpQ. apply in_map_iff in Hin as (pn & E & Hin). apply in_map_iff. exists pn. split; [exact E|].
              unfold lay_blocks. apply in_app_iff. left. apply HPin. exact Hin.
            - intros j Hj. apply Hk; swe_m_lia.
            - intros pn j Hpn Hj. apply HbQ; [apply in_app_iff; left; apply HPin; exact Hpn | exact Hj]. }
          { cbn [snd]. apply Forall_app. split; [exact HF | constructor; [exact Hlx | constructor]]. }
        * exfalso. assert (E : nth_error (r_calls R ++ [(REC_WORKER_ENV, A ++ [x])]) i = None)
          by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
          congruence.
    - split; [|exact C6].
      pose proof C5 as (_ & HL6 & _).
      apply (acall_at_kept (ablocks B ly S) _ rd); [exact C5 | | |].
      + intros pn Hpn. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
      + intros j Hj. apply Hk; swe_m_lia.
      + intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hpn. }
  split; [exact T1|]. split; [exact T2|]. split; [exact T3|].
  exact (swe_m_own_perm _ _ Q _ (p, Z.of_nat (length x) + 1) Hown Hperm HpQ Hapg Haps).
- (* the spill arm: the call is record.spill *)
  assert (Hn : length (r_calls R) = 16%nat) by lia.
  rewrite (rec_record_spill R REC_WORKER_ENV A Hn) in H.
  rewrite (rec_record_spill R REC_WORKER_ENV (A ++ [x]) Hn).
  rewrite Hn, swe_m_slot_16 in Hnargs, Harg, Hk.
  destruct H as (Q & HA & HO).
  assert (HblQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly S)) by (intros pn Hpn; apply Hbl0, HO, Hpn).
  assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
  by (intros [q k] i Hpn Hi; exact (Hb q k i (proj2 (HO (q, k)) Hpn) Hi)).
  assert (HpQ : ~ In p (map fst (lay_blocks Q))).
  { intros Hin. apply in_map_iff in Hin as ([q k] & E & Hin). cbn [fst] in E. exact (HpO q k (proj2 (HO (q, k)) Hin) E). }
  unfold lay_blocks in HblQ, HbQ.
  destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & HS & Hown).
  unfold set_spill in C1, C2, C3, C4, C5, C6. cbn [r_calls r_spill] in C1, C2, C3, C4, C5, C6.
  pose proof (swe_m_lay_spill Q (p, Z.of_nat (length x) + 1)) as Hperm.
  assert (Hg : forall a, (A_G_REC <= a < A_G_REC + 8 \/ A_G_REC + 912 <= a < A_G_REC + 960) -> rd' a = rd a)
  by (intros a Ha'; apply Hk; swe_m_lia).
  assert (Ht : forall pn i, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
  by (intros pn i Hpn Hi; apply HbQ; [apply in_app_iff; right; apply in_app_iff; right; exact Hpn | exact Hi]).
  destruct (swe_m_tail_kept _ rd rd' A_G_REC R Q Ha Hr HS Hg Ht) as (T1 & T2 & T3).
  exists (RLay (l_calls Q) (l_spill Q ++ [(p, Z.of_nat (length x) + 1)]) (l_answer Q) (l_reply Q)).
  split; [|exact (swe_m_iff_perm _ _ _ _ HO Hperm)].
  unfold arep_at. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  split.
  { unfold ag1_calls, set_spill. cbn [r_calls r_spill l_calls l_spill].
    split; [exact C1|]. split; [exact C2|].
    split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk'; apply Hk; swe_m_lia]|].
    split.
    - intros i c P Hc HP. destruct (C4 i c P Hc HP) as [HC HF]. split; [|exact HF].
      pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
      pose proof HC as (_ & HL6 & _).
      apply (acall_at_kept (ablocks B ly S) _ rd); [exact HC | | |].
      + intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ HP) | exact Hpn].
      + intros j Hj. apply Hk; swe_m_lia.
      + intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ HP) | exact Hpn].
    - split.
      + apply (swe_m_call_arg _ rd); [exact C5 | exact HA6 | exact Hpin | exact Hp0 | | exact Hlx | exact Hstr | exact Hnargs | exact Harg | | ].
        * intros Hin. apply HpQ. apply in_map_iff in Hin as (pn & E & Hin). apply in_map_iff. exists pn. split; [exact E|].
          unfold lay_blocks. apply in_app_iff. right. apply in_app_iff. left. exact Hin.
        * intros j Hj. apply Hk; swe_m_lia.
        * intros pn j Hpn Hj. apply HbQ; [apply in_app_iff; right; apply in_app_iff; left; exact Hpn | exact Hj].
      + cbn [snd]. apply Forall_app. split; [exact C6 | constructor; [exact Hlx | constructor]]. }
  split; [exact T1|]. split; [exact T2|]. split; [exact T3|].
  exact (swe_m_own_perm _ _ Q _ (p, Z.of_nat (length x) + 1) Hown Hperm HpQ Hapg Haps).
Qed.

End d.
