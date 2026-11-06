(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder facts of plugin-hostd/fuzz_command's sup_broadcast walk
   (sup_broadcast.v), over readers and block lists only: the recorder representation of CmdRep.v (rec_repA) after
   record() put the call (REC_BROADCAST, [s]) in table slot n or in record.spill and arg_line appended its one
   argument, and the block bookkeeping of the call's post-condition. The agree lemmas are those of the reply walk
   (lib/A/Prog/reply_s1.v), the recorder layout is lib/Prog/RecInv.v:9-37. *)
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
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* rec_repA (CmdRep.v:154) with the block list as a parameter: rec_repA B ly S rd R O is rec_repL (ablocks B ly S) rd R O *)
Definition rec_repL (bl : list (Z * Z)) (rd : reader) (R : rstate) (O : list (Z * Z)) : Prop :=
exists Q, arep_at bl rd A_G_REC A_REC_SPILL R Q /\ (forall pn, In pn O <-> In pn (lay_blocks Q)).

(* The agree lemmas below are copied from the reply walk,
   an earlier version of lib/A/Prog/reply_s1.v, lines 28-150. *)
Lemma aval_mem_agree : forall (rd rd' : reader) a n v,
aval_mem rd a n v -> (forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite Hk by lia. exact (H k Hkn). Qed.
Lemma abytes_atR_agree : forall (rd rd' : reader) p l n,
abytes_atR rd p l -> Z.of_nat (length l) <= n -> (forall k, 0 <= k < n -> rd' (p + k) = rd (p + k)) -> abytes_atR rd' p l.
Proof. intros rd rd' p l n H Hle Hk i Hi. rewrite Hk by lia. exact (H i Hi). Qed.
Lemma astr_atR_agree : forall (rd rd' : reader) p s n,
astr_atR rd p s -> Z.of_nat (length s) + 1 <= n -> (forall k, 0 <= k < n -> rd' (p + k) = rd (p + k)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s n [Hb Hn0] Hle Hk. split; [|exact Hn0].
apply (abytes_atR_agree rd rd' p _ n Hb); [rewrite length_app; cbn [length]; lia | exact Hk].
Qed.
Lemma acall_at_agree : forall bl bl' rd rd' a c P,
acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl -> In pn bl') ->
(forall k, 0 <= k < 8 + 8 * Z.of_nat (length P) -> rd' (a + k) = rd (a + k)) ->
(forall pn, In pn P -> forall k, 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & Hfn & Hna & Hnd & Hargs) HB HR HS.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_agree rd rd' _ 4 _ Hfn); intros k Hk; unfold CALL_OFF_FN; change (Z.of_nat 4) with 4 in Hk;
  replace (a + 0 + k) with (a + k) by lia; apply HR; lia|].
split; [apply (aval_mem_agree rd rd' _ 4 _ Hna); intros k Hk; unfold CALL_OFF_NARGS; change (Z.of_nat 4) with 4 in Hk;
  replace (a + 4 + k) with (a + (4 + k)) by lia; apply HR; lia|].
split; [exact Hnd|].
intros k s pn Hs Hpn. destruct (Hargs k s pn Hs Hpn) as (A1 & A2 & A3 & A4 & A5).
assert (Hk : (k < length P)%nat) by (apply nth_error_Some; rewrite Hpn; discriminate).
pose proof (nth_error_In _ _ Hpn) as HinP.
split; [|split; [exact A2|split; [exact (HB pn HinP A3)|split; [exact A4|]]]].
- apply (aval_mem_agree rd rd' _ 8 _ A1). intros kk Hkk. unfold CALL_OFF_ARGS. change (Z.of_nat 8) with 8 in Hkk.
  replace (a + 8 + 8 * Z.of_nat k + kk) with (a + (8 + 8 * Z.of_nat k + kk)) by lia. apply HR. lia.
- apply (astr_atR_agree rd rd' _ _ (snd pn) A5); [lia|]. exact (HS pn HinP).
Qed.
Lemma in_lay_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q i P pn Hi Hp. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hi) | exact Hp].
Qed.
Lemma in_lay_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma in_lay_answer : forall Q pn, l_answer Q = Some pn -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite H. left. reflexivity. Qed.
Lemma in_lay_reply : forall Q pn, l_reply Q = Some pn -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. rewrite H. left. reflexivity. Qed.
Lemma arep_at_agree : forall bl bl' rd rd' gr sc R Q,
arep_at bl rd gr sc R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl -> In pn bl') ->
(forall k, 0 <= k < REC_SIZE -> rd' (gr + k) = rd (gr + k)) ->
(forall k, 0 <= k < SC_SIZE -> rd' (sc + k) = rd (sc + k)) ->
(forall pn, In pn (lay_blocks Q) -> forall k, 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
arep_at bl' rd' gr sc R Q.
Proof.
intros bl bl' rd rd' gr sc R Q (Hg8 & Hs8 & Hap & HC & HA & HR & HSc & HOwn) HB HG HSP HO.
assert (VG : forall off n v, aval_mem rd (gr + off) n v -> 0 <= off -> off + Z.of_nat n <= REC_SIZE -> aval_mem rd' (gr + off) n v).
{ intros off n v H H0 H1. apply (aval_mem_agree rd rd' _ n _ H). intros k Hk.
  replace (gr + off + k) with (gr + (off + k)) by lia. apply HG. lia. }
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  split; [exact C1|]. split; [exact C2|]. split; [apply VG; [exact C3 | unfold OFF_NCALLS; lia | unfold OFF_NCALLS, REC_SIZE; cbn; lia]|].
  split; [|split; [|exact C6]].
  - intros i c P Hc HP. destruct (C4 i c P Hc HP) as [A F]. split; [|exact F].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    pose proof A as (_ & Hn6 & HlP & _).
    apply (acall_at_agree bl bl' rd rd' _ c P A).
    + intros pn Hpn. apply HB. exact (in_lay_calls Q i P pn HP Hpn).
    + intros k Hk. replace (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i + k) with (gr + (OFF_CALLS + CALL_SIZE * Z.of_nat i + k)) by lia.
      apply HG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE. rewrite HlP in Hk. lia.
    + intros pn Hpn. apply HO. exact (in_lay_calls Q i P pn HP Hpn).
  - pose proof C5 as (_ & Hn6 & HlP & _). apply (acall_at_agree bl bl' rd rd' _ _ _ C5).
    + intros pn Hpn. apply HB. exact (in_lay_spill Q pn Hpn).
    + intros k Hk. apply HSP. unfold SC_SIZE. rewrite HlP in Hk. lia.
    + intros pn Hpn. apply HO. exact (in_lay_spill Q pn Hpn). }
split.
{ unfold aanswer_at in *. destruct (r_answer R) as [x|] eqn:Ea, (l_answer Q) as [pn|] eqn:Eq; try contradiction.
  - destruct HA as (A1 & A2 & A3 & A4 & A5 & A6).
    split; [apply VG; [exact A1 | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, REC_SIZE; cbn; lia]|].
    split; [exact A2|]. split; [exact (HB pn (in_lay_answer Q pn Eq) A3)|]. split; [exact A4|]. split; [|exact A6].
    apply (astr_atR_agree rd rd' _ _ (snd pn) A5); [lia|]. exact (HO pn (in_lay_answer Q pn Eq)).
  - apply VG; [exact HA | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, REC_SIZE; cbn; lia]. }
split.
{ unfold areply_at in *. destruct (r_reply R) as [x|] eqn:Ea, (l_reply Q) as [pn|] eqn:Eq; try contradiction.
  - destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply VG; [exact A1 | unfold OFF_REPLY; lia | unfold OFF_REPLY, REC_SIZE; cbn; lia]|].
    split; [apply VG; [exact A2 | unfold OFF_REPLY_SIZE; lia | unfold OFF_REPLY_SIZE, REC_SIZE; cbn; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact (HB pn (in_lay_reply Q pn Eq) A5)|]. split; [exact A6|]. split; [|exact A8].
    apply (abytes_atR_agree rd rd' _ _ (snd pn) A7); [lia|]. exact (HO pn (in_lay_reply Q pn Eq)).
  - destruct HR as [A1 A2].
    split; apply VG; first [exact A1 | exact A2 | unfold OFF_REPLY, OFF_REPLY_SIZE; lia | unfold OFF_REPLY, OFF_REPLY_SIZE, REC_SIZE; cbn; lia]. }
split; [|exact HOwn].
destruct HSc as (S1 & S2 & S3 & S4 & S5 & REST).
split; [apply VG; [exact S1 | unfold OFF_REFUSE; lia | unfold OFF_REFUSE, REC_SIZE; cbn; lia]|].
split; [apply VG; [exact S2 | unfold OFF_CODE; lia | unfold OFF_CODE, REC_SIZE; cbn; lia]|].
split; [apply VG; [exact S3 | unfold OFF_NREPLIES; lia | unfold OFF_NREPLIES, REC_SIZE; cbn; lia]|].
split; [apply VG; [exact S4 | unfold OFF_STATE; lia | unfold OFF_STATE, REC_SIZE; cbn; lia]|].
split; [apply VG; [exact S5 | unfold OFF_HOST; lia | unfold OFF_HOST, REC_SIZE; cbn; lia] | exact REST].
Qed.
Lemma lay_blocks_in_bl : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> In pn bl.
Proof.
intros bl rd gr sc R Q pn (_ & _ & _ & HC & HA & HR & _) Hin.
unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hpn). apply In_nth_error in HP as (i & Hi).
  destruct HC as (C1 & C2 & _ & C4 & _).
  assert (Hi' : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_Some in Hi'; contradiction].
  destruct (C4 i c P Hc Hi) as ((_ & _ & HlP & _ & _ & _ & Hargs) & _).
  apply In_nth_error in Hpn as (k & Hk).
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hk'; contradiction].
  exact (proj1 (proj2 (proj2 (Hargs k s pn Hs Hk)))).
- apply in_app_or in Hin as [Hin | Hin].
  + destruct HC as (_ & _ & _ & _ & (_ & _ & HlP & _ & _ & _ & Hargs) & _).
    apply In_nth_error in Hin as (k & Hk).
    assert (Hk' : (k < length (snd (r_spill R)))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
    destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hk'; contradiction].
    exact (proj1 (proj2 (proj2 (Hargs k s pn Hs Hk)))).
  + apply in_app_or in Hin as [Hin | Hin].
    * unfold aanswer_at in HA. destruct (l_answer Q) as [pn'|]; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_answer R); [exact (proj1 (proj2 (proj2 HA))) | contradiction].
    * unfold areply_at in HR. destruct (l_reply Q) as [pn'|]; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_reply R); [exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))) | contradiction].
Qed.

(* every block of the recorder's layout has at least one byte (the shape of lay_blocks_in_bl above) *)
Lemma lay_blocks_pos : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> 0 < snd pn.
Proof.
intros bl rd gr sc R Q pn (_ & _ & _ & HC & HA & HR & _) Hin.
unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hpn). apply In_nth_error in HP as (i & Hi).
  destruct HC as (C1 & C2 & _ & C4 & _).
  assert (Hi' : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_Some in Hi'; contradiction].
  destruct (C4 i c P Hc Hi) as ((_ & _ & HlP & _ & _ & _ & Hargs) & _).
  apply In_nth_error in Hpn as (k & Hk).
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hk'; contradiction].
  destruct (Hargs k s pn Hs Hk) as (_ & _ & _ & A4 & _). lia.
- apply in_app_or in Hin as [Hin | Hin].
  + destruct HC as (_ & _ & _ & _ & (_ & _ & HlP & _ & _ & _ & Hargs) & _).
    apply In_nth_error in Hin as (k & Hk).
    assert (Hk' : (k < length (snd (r_spill R)))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
    destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hk'; contradiction].
    destruct (Hargs k s pn Hs Hk) as (_ & _ & _ & A4 & _). lia.
  + apply in_app_or in Hin as [Hin | Hin].
    * unfold aanswer_at in HA. destruct (l_answer Q) as [pn'|]; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_answer R); [|contradiction]. destruct HA as (_ & _ & _ & A4 & _). lia.
    * unfold areply_at in HR. destruct (l_reply Q) as [pn'|]; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_reply R) as [x|]; [|contradiction]. destruct HR as (_ & _ & _ & A4 & _ & A6 & _).
      destruct x as [|b x]; [contradiction|]. cbn [length] in A6. lia.
Qed.

(* the recorder representation after a change of the call table / spill slot only: answer, reply and the scalars
   are read again through rd', which agrees with rd on g_rec bytes [0, 8) and [912, 960) and on the recorder's blocks *)
Lemma arep_at_upd : forall bl bl' rd rd' gr sc R Q R' Q',
arep_at bl rd gr sc R Q ->
ag1_calls bl' rd' gr sc R' Q' -> ag1_own gr sc Q' ->
r_answer R' = r_answer R -> l_answer Q' = l_answer Q ->
r_reply R' = r_reply R -> l_reply Q' = l_reply Q ->
r_refuse R' = r_refuse R -> r_code R' = r_code R -> r_nreplies R' = r_nreplies R ->
r_state R' = r_state R -> r_host R' = r_host R ->
(forall pn, In pn (lay_blocks Q) -> In pn bl -> In pn bl') ->
(forall k, (0 <= k < 8 \/ 912 <= k < 960) -> rd' (gr + k) = rd (gr + k)) ->
(forall pn, In pn (lay_blocks Q) -> forall k, 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
arep_at bl' rd' gr sc R' Q'.
Proof.
intros bl bl' rd rd' gr sc R Q R' Q' (Hg8 & Hs8 & Hap & _ & HA & HR & HSc & _) HC HOwn
  Ea Eqa Er Eqr E1 E2 E3 E4 E5 HB HG HO.
assert (VG : forall off n v, aval_mem rd (gr + off) n v ->
  (0 <= off /\ off + Z.of_nat n <= 8 \/ 912 <= off /\ off + Z.of_nat n <= 960) -> aval_mem rd' (gr + off) n v).
{ intros off n v H H0. apply (aval_mem_agree rd rd' _ n _ H). intros k Hk.
  replace (gr + off + k) with (gr + (off + k)) by lia. apply HG. lia. }
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split; [exact HC|].
split.
{ unfold aanswer_at in *. rewrite Ea, Eqa.
  destruct (r_answer R) as [x|] eqn:Ea', (l_answer Q) as [pn|] eqn:Eq; try contradiction.
  - destruct HA as (A1 & A2 & A3 & A4 & A5 & A6).
    split; [apply VG; [exact A1 | unfold OFF_ANSWER; cbn; lia]|].
    split; [exact A2|]. split; [exact (HB pn (in_lay_answer Q pn Eq) A3)|]. split; [exact A4|]. split; [|exact A6].
    apply (astr_atR_agree rd rd' _ _ (snd pn) A5); [lia|]. exact (HO pn (in_lay_answer Q pn Eq)).
  - apply VG; [exact HA | unfold OFF_ANSWER; cbn; lia]. }
split.
{ unfold areply_at in *. rewrite Er, Eqr.
  destruct (r_reply R) as [x|] eqn:Ea', (l_reply Q) as [pn|] eqn:Eq; try contradiction.
  - destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply VG; [exact A1 | unfold OFF_REPLY; cbn; lia]|].
    split; [apply VG; [exact A2 | unfold OFF_REPLY_SIZE; cbn; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact (HB pn (in_lay_reply Q pn Eq) A5)|]. split; [exact A6|]. split; [|exact A8].
    apply (abytes_atR_agree rd rd' _ _ (snd pn) A7); [lia|]. exact (HO pn (in_lay_reply Q pn Eq)).
  - destruct HR as [A1 A2].
    split; apply VG; first [exact A1 | exact A2 | unfold OFF_REPLY, OFF_REPLY_SIZE; cbn; lia]. }
split; [|exact HOwn].
destruct HSc as (S1 & S2 & S3 & S4 & S5 & REST).
unfold ag1_scalars. rewrite E1, E2, E3, E4, E5.
split; [apply VG; [exact S1 | unfold OFF_REFUSE; cbn; lia]|].
split; [apply VG; [exact S2 | unfold OFF_CODE; cbn; lia]|].
split; [apply VG; [exact S3 | unfold OFF_NREPLIES; cbn; lia]|].
split; [apply VG; [exact S4 | unfold OFF_STATE; cbn; lia]|].
split; [apply VG; [exact S5 | unfold OFF_HOST; cbn; lia] | exact REST].
Qed.

(* `NoDup` and `∈` here are stdpp's (base.v); the bridges to Stdlib's In / List.NoDup. sb_elem_of_In is the one of
   the sup_broadcast walk. *)
Lemma sb_elem_of_In : forall {A : Type} (x : A) (l : list A), x ∈ l <-> In x l.
Proof.
intros A x l. induction l as [|y l IH]; split; intros H.
- inversion H.
- destruct H.
- inversion H; subst; [left; reflexivity | right; apply IH; assumption].
- destruct H as [<- | H]; [constructor | constructor; apply IH; exact H].
Qed.
Lemma sb_NoDup_iff : forall {A : Type} (l : list A), NoDup l <-> List.NoDup l.
Proof.
intros A l. induction l as [|y l IH]; split; intros H.
- constructor.
- constructor.
- inversion H; subst. constructor; [|apply IH; assumption].
  intros Hy. match goal with Hn : ~ y ∈ l |- _ => apply Hn end. apply sb_elem_of_In. exact Hy.
- inversion H; subst. constructor; [|apply IH; assumption].
  intros Hy. match goal with Hn : ~ In y l |- _ => apply Hn end. apply sb_elem_of_In. exact Hy.
Qed.

(* the call (REC_BROADCAST, [s]) with its one argument block (p, k), at a call record a *)
Lemma acall_at_one : forall bl rd a p k s,
aval_mem rd (a + CALL_OFF_FN) 4 REC_BROADCAST -> aval_mem rd (a + CALL_OFF_NARGS) 4 1 ->
aval_mem rd (a + CALL_OFF_ARGS) 8 p ->
In (p, k) bl -> 4096 <= p -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 -> astr_atR rd p s ->
acall_at bl rd a (REC_BROADCAST, [s]) [(p, k)].
Proof.
intros bl rd a p k s Hfn Hna Harg Hin Hp Hk Hs.
unfold acall_at. cbn [fst snd length map].
split; [unfold REC_BROADCAST, REC_FN_COUNT; lia|].
split; [lia|]. split; [reflexivity|].
split; [exact Hfn|]. split; [exact Hna|].
split; [apply sb_NoDup_iff; constructor; [intros []|constructor]|].
intros kk s0 pn H1 H2. destruct kk as [|[|kk]]; cbn in H1, H2; try discriminate.
injection H1 as <-. injection H2 as <-. cbn [fst snd].
split; [replace (a + CALL_OFF_ARGS + 8 * Z.of_nat 0) with (a + CALL_OFF_ARGS) by lia; exact Harg|].
split; [lia|]. split; [exact Hin|]. split; [exact Hk|]. exact Hs.
Qed.

(* ag1_calls after record() appended the call to table slot n *)
Lemma ag1_calls_slot : forall bl bl' rd rd' gr sc R Q n p k s,
ag1_calls bl rd gr sc R Q -> n = length (r_calls R) -> (n < 16)%nat ->
(forall j, 0 <= j < REC_SIZE -> ~ (OFF_NCALLS <= j < OFF_NCALLS + 4) ->
 ~ (OFF_CALLS + CALL_SIZE * Z.of_nat n <= j < OFF_CALLS + CALL_SIZE * Z.of_nat n + 16) ->
 rd' (gr + j) = rd (gr + j)) ->
(forall j, 0 <= j < SC_SIZE -> rd' (sc + j) = rd (sc + j)) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl -> In pn bl') ->
(forall pn, In pn (lay_blocks Q) -> forall j, 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
aval_mem rd' (gr + OFF_NCALLS) 4 (Z.of_nat n + 1) ->
acall_at bl' rd' (gr + OFF_CALLS + CALL_SIZE * Z.of_nat n) (REC_BROADCAST, [s]) [(p, k)] ->
Z.of_nat (length s) <= LMAX ->
ag1_calls bl' rd' gr sc (set_calls R (r_calls R ++ [(REC_BROADCAST, [s])]))
  (RLay (l_calls Q ++ [[(p, k)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
Proof.
intros bl bl' rd rd' gr sc R Q n p k s (C1 & C2 & C3 & C4 & C5 & C6) En Hn HG HSP HB HO Hnc Hnew Hs.
unfold ag1_calls. cbn [r_calls r_spill set_calls l_calls l_spill].
split; [rewrite length_app; cbn [length]; lia|].
split; [rewrite !length_app, C2; reflexivity|].
split; [replace (Z.of_nat (length (r_calls R ++ [(REC_BROADCAST, [s])]))) with (Z.of_nat n + 1)
  by (rewrite length_app; cbn [length]; lia); exact Hnc|].
split; [|split; [|exact C6]].
- intros i c P Hc HP. destruct (Nat.lt_ge_cases i n) as [Hi | Hi].
  + rewrite List.nth_error_app1 in Hc by lia. rewrite List.nth_error_app1 in HP by lia.
    destruct (C4 i c P Hc HP) as [A F]. split; [|exact F].
    pose proof A as (_ & Hn6 & HlP & _).
    apply (acall_at_agree bl bl' rd rd' _ c P A).
    * intros pn Hpn. apply HB. exact (in_lay_calls Q i P pn HP Hpn).
    * intros j Hj. replace (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i + j) with (gr + (OFF_CALLS + CALL_SIZE * Z.of_nat i + j)) by lia.
      rewrite HlP in Hj. apply HG; unfold OFF_CALLS, OFF_NCALLS, CALL_SIZE, REC_SIZE; lia.
    * intros pn Hpn. apply HO. exact (in_lay_calls Q i P pn HP Hpn).
  + assert (Hlt : (i < length (r_calls R ++ [(REC_BROADCAST, [s])]))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    rewrite length_app in Hlt. cbn [length] in Hlt.
    assert (Ei : i = n) by lia. subst i.
    rewrite List.nth_error_app2 in Hc by lia. rewrite List.nth_error_app2 in HP by lia.
    replace (n - length (r_calls R))%nat with O in Hc by lia.
    replace (n - length (l_calls Q))%nat with O in HP by lia.
    cbn in Hc, HP. injection Hc as <-. injection HP as <-.
    split; [exact Hnew|]. cbn [snd]. constructor; [exact Hs | constructor].
- pose proof C5 as (_ & Hn6 & HlP & _). apply (acall_at_agree bl bl' rd rd' _ _ _ C5).
  + intros pn Hpn. apply HB. exact (in_lay_spill Q pn Hpn).
  + intros j Hj. apply HSP. unfold SC_SIZE. rewrite HlP in Hj. lia.
  + intros pn Hpn. apply HO. exact (in_lay_spill Q pn Hpn).
Qed.

(* ag1_calls after record() put the call in record.spill *)
Lemma ag1_calls_spill : forall bl bl' rd rd' gr sc R Q p k s,
ag1_calls bl rd gr sc R Q ->
(forall j, 0 <= j < REC_SIZE -> rd' (gr + j) = rd (gr + j)) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl -> In pn bl') ->
(forall pn, In pn (lay_blocks Q) -> forall j, 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
acall_at bl' rd' sc (REC_BROADCAST, [s]) [(p, k)] ->
Z.of_nat (length s) <= LMAX ->
ag1_calls bl' rd' gr sc (set_spill R (REC_BROADCAST, [s])) (RLay (l_calls Q) [(p, k)] (l_answer Q) (l_reply Q)).
Proof.
intros bl bl' rd rd' gr sc R Q p k s (C1 & C2 & C3 & C4 & C5 & C6) HG HB HO Hnew Hs.
unfold ag1_calls. cbn [r_calls r_spill set_spill l_calls l_spill].
split; [exact C1|]. split; [exact C2|].
split; [apply (aval_mem_agree rd rd' _ 4 _ C3); intros j Hj; cbn in Hj;
  replace (gr + OFF_NCALLS + j) with (gr + (OFF_NCALLS + j)) by lia; apply HG; unfold OFF_NCALLS, REC_SIZE; lia|].
split; [|split; [exact Hnew | cbn [snd]; constructor; [exact Hs | constructor]]].
intros i c P Hc HP. destruct (C4 i c P Hc HP) as [A F]. split; [|exact F].
pose proof A as (_ & Hn6 & HlP & _).
assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
apply (acall_at_agree bl bl' rd rd' _ c P A).
- intros pn Hpn. apply HB. exact (in_lay_calls Q i P pn HP Hpn).
- intros j Hj. replace (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i + j) with (gr + (OFF_CALLS + CALL_SIZE * Z.of_nat i + j)) by lia.
  apply HG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE. rewrite HlP in Hj. lia.
- intros pn Hpn. apply HO. exact (in_lay_calls Q i P pn HP Hpn).
Qed.

(* the recorder's blocks gain one block (p, k), inserted in the middle of the layout's block list *)
Lemma own_add : forall gr sc Q Q' A B p k,
ag1_own gr sc Q -> lay_blocks Q = A ++ B -> lay_blocks Q' = A ++ (p, k) :: B ->
(forall pn, In pn (lay_blocks Q) -> fst pn <> p) ->
iv_apart p k gr REC_SIZE -> iv_apart p k sc SC_SIZE -> ag1_own gr sc Q'.
Proof.
intros gr sc Q Q' A B p k (ND & Hap) EQ EQ' Hne Hg Hs. split.
- rewrite EQ'. rewrite EQ in ND, Hne. apply sb_NoDup_iff. apply sb_NoDup_iff in ND.
  eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_middle|].
  cbn [map fst]. constructor; [|exact ND].
  intros Hin. apply List.in_map_iff in Hin as (pn & Hpn & Hin). exact (Hne pn Hin Hpn).
- intros pn Hin. rewrite EQ' in Hin. apply in_app_or in Hin as [Hin | [<- | Hin]].
  + apply Hap. rewrite EQ. apply in_or_app. left. exact Hin.
  + cbn [fst snd]. split; assumption.
  + apply Hap. rewrite EQ. apply in_or_app. right. exact Hin.
Qed.

Lemma O_add : forall (O : list (Z * Z)) Q Q' A B p k,
(forall pn, In pn O <-> In pn (lay_blocks Q)) -> lay_blocks Q = A ++ B -> lay_blocks Q' = A ++ (p, k) :: B ->
forall pn, In pn (O ++ [(p, k)]) <-> In pn (lay_blocks Q').
Proof.
intros O Q Q' A B p k HO EQ EQ' pn. rewrite EQ', List.in_app_iff, HO, EQ, !List.in_app_iff. cbn [In]. tauto.
Qed.

(* two blocks of a list without repeated starts that have the same start are the same block *)
Lemma nodup_fst_same : forall (l : list (Z * Z)) x y, List.NoDup (map fst l) -> In x l -> In y l -> fst x = fst y -> x = y.
Proof.
intros l. induction l as [|a l IH]; intros x y ND Hx Hy E; [destruct Hx|].
cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
destruct Hx as [<- | Hx], Hy as [<- | Hy].
- reflexivity.
- exfalso. apply NI. rewrite E. apply List.in_map. exact Hy.
- exfalso. apply NI. rewrite <- E. apply List.in_map. exact Hx.
- exact (IH x y ND Hx Hy E).
Qed.

Lemma nodup_fst_disj : forall (l1 l2 : list (Z * Z)) x, List.NoDup (map fst (l1 ++ l2)) -> In x l1 -> In x l2 -> False.
Proof.
intros l1. induction l1 as [|a l1 IH]; intros l2 x ND H1 H2; [destruct H1|].
cbn [app map] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
destruct H1 as [<- | H1].
- apply NI. apply List.in_map. apply in_or_app. right. exact H2.
- exact (IH l2 x ND H1 H2).
Qed.

Lemma zz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof.
intros [a b] [c d]. destruct (Z.eq_dec a c) as [Ea | Na].
- destruct (Z.eq_dec b d) as [Eb | Nb].
  + left. subst. reflexivity.
  + right. intros E. injection E as _ E. exact (Nb E).
- right. intros E. injection E as E _. exact (Na E).
Qed.

(* sb_rep_pos's content, here so the two record lemmas below can use it *)
Lemma rec_repL_pos : forall bl rd R O pn, rec_repL bl rd R O -> In pn O -> 0 < snd pn /\ In pn bl.
Proof.
intros bl rd R O pn (Q & HA & HO) Hin. apply HO in Hin. split.
- exact (lay_blocks_pos _ _ _ _ _ _ _ HA Hin).
- exact (lay_blocks_in_bl _ _ _ _ _ _ _ HA Hin).
Qed.

(* record() into table slot n (n < 16), then arg_line's one argument p (a block of k bytes holding s) *)
Lemma sb_rep_slot : forall bl rd bl' rd' R O n p k s,
rec_repL bl rd R O ->
n = length (r_calls R) -> (n < 16)%nat ->
(forall j, 0 <= j < REC_SIZE -> ~ (OFF_NCALLS <= j < OFF_NCALLS + 4) ->
 ~ (OFF_CALLS + CALL_SIZE * Z.of_nat n <= j < OFF_CALLS + CALL_SIZE * Z.of_nat n + 16) ->
 rd' (A_G_REC + j) = rd (A_G_REC + j)) ->
(forall j, 0 <= j < SC_SIZE -> rd' (A_REC_SPILL + j) = rd (A_REC_SPILL + j)) ->
(forall pn, In pn O -> forall j, 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
(forall pn, In pn O -> In pn bl -> In pn bl') ->
aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat n + 1) ->
aval_mem rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n + CALL_OFF_FN) 4 REC_BROADCAST ->
aval_mem rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n + CALL_OFF_NARGS) 4 1 ->
aval_mem rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n + CALL_OFF_ARGS) 8 p ->
In (p, k) bl' -> 4096 <= p -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 -> Z.of_nat (length s) <= LMAX ->
astr_atR rd' p s ->
(forall pn, In pn O -> iv_apart p k (fst pn) (snd pn)) ->
iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
rec_repL bl' rd' (rec_record R REC_BROADCAST [s]) (O ++ [(p, k)]).
Proof.
intros bl rd bl' rd' R O n p k s HR0 En Hn HG HSP HOb HB Hnc Hfn Hna Harg Hin Hp Hk Hs Hstr Hap Hapg Haps.
pose proof (fun pn H => rec_repL_pos bl rd R O pn HR0 H) as Hpos.
destruct HR0 as (Q & HA & HO).
pose proof HA as (_ & _ & _ & HC & _ & _ & _ & HOwn).
rewrite rec_record_calls by lia.
set (Q' := RLay (l_calls Q ++ [[(p, k)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
assert (EQ : lay_blocks Q = concat (l_calls Q) ++ (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))) by reflexivity.
assert (EQ' : lay_blocks Q' = concat (l_calls Q) ++ (p, k) :: (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))).
{ unfold Q', lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite List.concat_app, <- List.app_assoc. reflexivity. }
unfold rec_repL. exists Q'. split.
- refine (arep_at_upd bl bl' rd rd' A_G_REC A_REC_SPILL R Q (set_calls R (r_calls R ++ [(REC_BROADCAST, [s])])) Q'
    HA _ _ eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl _ _ _).
  + apply (ag1_calls_slot bl bl' rd rd' A_G_REC A_REC_SPILL R Q n p k s HC En Hn HG HSP).
    * intros pn H1 H2. apply HB; [apply HO; exact H1 | exact H2].
    * intros pn H1. apply HOb. apply HO. exact H1.
    * exact Hnc.
    * apply acall_at_one; assumption.
    * exact Hs.
  + apply (own_add A_G_REC A_REC_SPILL Q Q' _ _ p k HOwn EQ EQ'); [|exact Hapg|exact Haps].
    intros pn H1 E. apply HO in H1. pose proof (Hap pn H1) as H2. pose proof (proj1 (Hpos pn H1)) as H3.
    unfold iv_apart in H2. lia.
  + intros pn H1 H2. apply HB; [apply HO; exact H1 | exact H2].
  + intros j Hj. apply HG; unfold OFF_NCALLS, OFF_CALLS, CALL_SIZE, REC_SIZE; lia.
  + intros pn H1. apply HOb. apply HO. exact H1.
- exact (O_add O Q Q' _ _ p k HO EQ EQ').
Qed.

(* record() into record.spill (after rec_calls_free emptied its arguments), then arg_line's one argument *)
Lemma sb_rep_spill : forall bl rd bl' rd' R O p k s,
rec_repL bl rd R O -> snd (r_spill R) = [] ->
(forall j, 0 <= j < REC_SIZE -> rd' (A_G_REC + j) = rd (A_G_REC + j)) ->
(forall j, 16 <= j < SC_SIZE -> rd' (A_REC_SPILL + j) = rd (A_REC_SPILL + j)) ->
(forall pn, In pn O -> forall j, 0 <= j < snd pn -> rd' (fst pn + j) = rd (fst pn + j)) ->
(forall pn, In pn O -> In pn bl -> In pn bl') ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 REC_BROADCAST ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 1 ->
aval_mem rd' (A_REC_SPILL + CALL_OFF_ARGS) 8 p ->
In (p, k) bl' -> 4096 <= p -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 -> Z.of_nat (length s) <= LMAX ->
astr_atR rd' p s ->
(forall pn, In pn O -> iv_apart p k (fst pn) (snd pn)) ->
iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
rec_repL bl' rd' (set_spill R (REC_BROADCAST, [s])) (O ++ [(p, k)]).
Proof.
intros bl rd bl' rd' R O p k s HR0 Hsp HG HSP HOb HB Hfn Hna Harg Hin Hp Hk Hs Hstr Hap Hapg Haps.
pose proof (fun pn H => rec_repL_pos bl rd R O pn HR0 H) as Hpos.
destruct HR0 as (Q & HA & HO).
pose proof HA as (_ & _ & _ & HC & _ & _ & _ & HOwn).
assert (Hls : l_spill Q = []).
{ destruct HC as (_ & _ & _ & _ & (_ & _ & HlP & _) & _). rewrite Hsp in HlP. cbn [length] in HlP.
  apply List.length_zero_iff_nil. exact HlP. }
set (Q' := RLay (l_calls Q) [(p, k)] (l_answer Q) (l_reply Q)).
assert (EQ : lay_blocks Q = concat (l_calls Q) ++ (oblk (l_answer Q) ++ oblk (l_reply Q))).
{ unfold lay_blocks. rewrite Hls. reflexivity. }
assert (EQ' : lay_blocks Q' = concat (l_calls Q) ++ (p, k) :: (oblk (l_answer Q) ++ oblk (l_reply Q))) by reflexivity.
unfold rec_repL. exists Q'. split.
- refine (arep_at_upd bl bl' rd rd' A_G_REC A_REC_SPILL R Q (set_spill R (REC_BROADCAST, [s])) Q'
    HA _ _ eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl _ _ _).
  + apply (ag1_calls_spill bl bl' rd rd' A_G_REC A_REC_SPILL R Q p k s HC HG).
    * intros pn H1 H2. apply HB; [apply HO; exact H1 | exact H2].
    * intros pn H1. apply HOb. apply HO. exact H1.
    * apply acall_at_one; assumption.
    * exact Hs.
  + apply (own_add A_G_REC A_REC_SPILL Q Q' _ _ p k HOwn EQ EQ'); [|exact Hapg|exact Haps].
    intros pn H1 E. apply HO in H1. pose proof (Hap pn H1) as H2. pose proof (proj1 (Hpos pn H1)) as H3.
    unfold iv_apart in H2. lia.
  + intros pn H1 H2. apply HB; [apply HO; exact H1 | exact H2].
  + intros j Hj. apply HG. unfold REC_SIZE. lia.
  + intros pn H1. apply HOb. apply HO. exact H1.
- exact (O_add O Q Q' _ _ p k HO EQ EQ').
Qed.

(* every block the representation names has at least one byte *)
Lemma sb_rep_pos : forall bl rd R O pn, rec_repL bl rd R O -> In pn O -> 0 < snd pn /\ In pn bl.
Proof. exact rec_repL_pos. Qed.

(* the old answer: the value g_rec.answer holds, 0 or the start of one of the recorder's blocks *)
Lemma sb_rep_old : forall bl rd R O, rec_repL bl rd R O ->
exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists ko, In (old, ko) O).
Proof.
intros bl rd R O (Q & HA & HO).
pose proof HA as (_ & _ & _ & _ & HAn & _).
unfold aanswer_at in HAn. destruct (r_answer R) as [x|] eqn:Ea, (l_answer Q) as [[q m]|] eqn:Eq; try contradiction.
- exists q. split; [exact (proj1 HAn)|]. right. exists m. apply HO. exact (in_lay_answer Q (q, m) Eq).
- exists 0. split; [exact HAn | left; reflexivity].
Qed.

(* the block bookkeeping of the post-condition. bl0: the blocks at the entry, O the recorder's; rec_calls_free frees
   F (empty on the table arm) leaving bl1; arg_line adds (p, k) giving bl2; answer frees the old answer (start old)
   and adds its two copies (p1, n) and (p2, n) giving bl3; the recorder's blocks become Omid ++ [(p, k)] after
   record() and arg_line, and O' after answer. *)
Lemma sb_post_blocks : forall (bl0 bl1 bl2 bl3 O Omid F O' : list (Z * Z)) (p k p1 p2 n old : Z),
NoDup (map fst bl0) -> NoDup (map fst bl2) -> NoDup (map fst bl3) ->
(forall pn, In pn O -> In pn bl0) ->
Permutation bl0 (bl1 ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn Omid -> In pn O) -> (forall pn, In pn O -> In pn Omid \/ In pn F) ->
(forall pn, In pn Omid -> In pn bl2) ->
Permutation bl2 ((p, k) :: bl1) -> Forall (fun qk => iv_apart p k (fst qk) (snd qk)) bl1 -> 0 < k ->
(forall pn, In pn bl3 <-> (In pn bl2 /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
(forall pn, In pn bl2 -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) -> p1 <> p2 ->
(forall pn, In pn O' <-> (In pn (Omid ++ [(p, k)]) /\ fst pn <> old) \/ pn = (p1, n)) ->
(old = 0 \/ exists ko, In (old, ko) (Omid ++ [(p, k)])) ->
(forall pn, In pn bl0 -> fst pn <> 0) ->
(forall pn, In pn O' -> In pn bl3) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn bl0) /\
(forall pn, In pn bl3 -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = (p2, n)) /\
(forall pn, In pn bl0 -> ~ In pn O -> In pn bl3) /\
In (p2, n) bl3 /\ (forall pn, In pn bl0 -> ~ In pn O -> pn <> (p2, n)) /\
~ In p2 (map fst O').
Proof.
intros bl0 bl1 bl2 bl3 O Omid F O' p k p1 p2 n old ND0 ND2 ND3 HO0 HP0 HFO HMO HOMF HM2 HP2 HAp Hk
  H3 Hn Hp12 HO' Hold Hnz HO'3.
apply sb_NoDup_iff in ND0, ND2, ND3.
assert (Hb0 : forall pn, In pn bl0 -> In pn bl1 \/ In pn F).
{ intros pn H. apply in_app_or. exact (Permutation_in _ HP0 H). }
assert (Hb1 : forall pn, In pn bl1 -> In pn bl0).
{ intros pn H. apply (Permutation_in _ (Permutation_sym HP0)). apply in_or_app. left. exact H. }
assert (Hb12 : forall pn, In pn bl1 -> In pn bl2).
{ intros pn H. apply (Permutation_in _ (Permutation_sym HP2)). right. exact H. }
assert (Hpk2 : In (p, k) bl2).
{ apply (Permutation_in _ (Permutation_sym HP2)). left. reflexivity. }
assert (Hb2 : forall pn, In pn bl2 -> pn = (p, k) \/ In pn bl1).
{ intros pn H. apply (Permutation_in _ HP2) in H. destruct H as [<- | H]; [left; reflexivity | right; exact H]. }
assert (ND01 : List.NoDup (map fst (bl1 ++ F))).
{ eapply Permutation_NoDup; [apply Permutation_map; exact HP0 | exact ND0]. }
assert (Hdisj : forall pn, In pn bl1 -> In pn F -> False).
{ intros pn H1 H2. exact (nodup_fst_disj bl1 F pn ND01 H1 H2). }
assert (Hpk1 : ~ In (p, k) bl1).
{ intros H. rewrite List.Forall_forall in HAp. specialize (HAp _ H). cbn [fst snd] in HAp. unfold iv_apart in HAp. lia. }
assert (HOx : forall pn, In pn bl0 -> fst pn = old -> In pn O).
{ intros pn H E. destruct Hold as [Ho | (ko & Hko)].
  - exfalso. exact (Hnz pn H (eq_trans E Ho)).
  - apply in_app_or in Hko as [Hko | [Epk | []]].
    + assert (Hko0 : In (old, ko) bl0) by (apply HO0; apply HMO; exact Hko).
      rewrite (nodup_fst_same bl0 pn (old, ko) ND0 H Hko0 E). apply HMO. exact Hko.
    + injection Epk as Ep _. destruct (Hb0 pn H) as [H1 | HF]; [exfalso | exact (HFO pn HF)].
      assert (Epn : pn = (p, k)) by (apply (nodup_fst_same bl2); [exact ND2 | exact (Hb12 pn H1) | exact Hpk2 | cbn [fst]; congruence]).
      subst pn. exact (Hpk1 H1). }
split.
{ intros pn H. apply HO' in H. destruct H as [(H & _) | ->].
  - apply in_app_or in H as [H | [<- | []]].
    + left. apply HMO. exact H.
    + destruct (in_dec zz_eq_dec (p, k) bl0) as [Hin | Hnin]; [|right; exact Hnin].
      left. destruct (Hb0 _ Hin) as [H1 | HF]; [exfalso; exact (Hpk1 H1) | exact (HFO _ HF)].
  - destruct (in_dec zz_eq_dec (p1, n) bl0) as [Hin | Hnin]; [|right; exact Hnin].
    left. destruct (Z.eq_dec p1 old) as [E | E]; [exact (HOx _ Hin E)|].
    destruct (Hb0 _ Hin) as [H1 | HF]; [exfalso; exact (proj1 (Hn _ (Hb12 _ H1) E) eq_refl) | exact (HFO _ HF)]. }
split.
{ intros pn H. apply H3 in H. destruct H as [(H & Hne) | [-> | ->]].
  - apply Hb2 in H as [-> | H].
    + right. left. apply HO'. left. split; [apply in_or_app; right; left; reflexivity | exact Hne].
    + destruct (in_dec zz_eq_dec pn O) as [HinO | HnO].
      * apply HOMF in HinO as [HM | HF].
        -- right. left. apply HO'. left. split; [apply in_or_app; left; exact HM | exact Hne].
        -- exfalso. exact (Hdisj pn H HF).
      * left. split; [apply Hb1; exact H | exact HnO].
  - right. left. apply HO'. right. reflexivity.
  - right. right. reflexivity. }
split.
{ intros pn H HnO. apply H3. left. split.
  - destruct (Hb0 pn H) as [H1 | HF]; [exact (Hb12 pn H1) | exfalso; exact (HnO (HFO pn HF))].
  - intros E. exact (HnO (HOx pn H E)). }
split; [apply H3; right; right; reflexivity|].
split.
{ intros pn H HnO Epn. destruct (Hb0 _ H) as [H1 | HF]; [|exact (HnO (HFO _ HF))].
  assert (E : fst pn <> old) by (intros E; exact (HnO (HOx pn H E))).
  exact (proj2 (Hn pn (Hb12 _ H1) E) Epn). }
intros H. apply List.in_map_iff in H as (pn & Ep & Hpn).
assert (E : pn = (p2, n)).
{ apply (nodup_fst_same bl3); [exact ND3 | exact (HO'3 pn Hpn) | apply H3; right; right; reflexivity | exact Ep]. }
subst pn. apply HO' in Hpn as [(Hm & Hne) | E].
- cbn [fst] in Hne. apply in_app_or in Hm as [Hm | [E | []]].
  + exact (proj2 (Hn _ (HM2 _ Hm) Hne) eq_refl).
  + injection E as Epp Ekk. subst p k. exact (proj2 (Hn _ Hpk2 Hne) eq_refl).
- exact (Hp12 (eq_sym (f_equal fst E))).
Qed.
